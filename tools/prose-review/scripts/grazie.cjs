#!/usr/bin/env node
// Drive the official signed-in extension UI; never replay authenticated requests.
const fs = require('fs');
const WebSocket = require('ws');
const delay = ms => new Promise(r => setTimeout(r, ms));
const endpoint = 'https://api.jetbrains.ai/user/v5/gec/correct/v4';
// ProseMirror interprets Markdown list/emphasis punctuation when text is inserted.
function editorProse(text) {return text.replace(/^[-*] /,'').replace(/\*{1,2}([^*]+)\*{1,2}/g,'$1');}
async function connect(target, onResponse) {
  const ws = new WebSocket(target.webSocketDebuggerUrl);
  await new Promise((r,j) => { ws.once('open',r); ws.once('error',j); });
  let next = 0; const pending = new Map();
  const call = (method,params={}) => new Promise((resolve,reject) => {
    const id = ++next;
    const timer = setTimeout(() => {pending.delete(id);reject(Error('CDP timeout'));},15000);
    pending.set(id,m => {clearTimeout(timer);m.error?reject(Error(m.error.message)):resolve(m.result);});
    ws.send(JSON.stringify({id,method,params}));
  });
  const responses = new Map();
  ws.on('message',raw => {
    const m = JSON.parse(raw);
    if(m.id) {pending.get(m.id)?.(m);pending.delete(m.id);return;}
    // Discard headers, request bodies and unrelated traffic without recording them.
    if(m.method==='Network.responseReceived' && m.params.response.url===endpoint)
      responses.set(m.params.requestId,m.params.response.status);
    if(m.method==='Network.loadingFinished' && responses.has(m.params.requestId)) {
      const status=responses.get(m.params.requestId);responses.delete(m.params.requestId);
      call('Network.getResponseBody',{requestId:m.params.requestId}).then(body => {
        onResponse({endpoint,status,body:JSON.parse(body.base64Encoded?Buffer.from(body.body,'base64').toString():body.body)});
      }).catch(e => onResponse({error:e.message}));
    }
  });
  await call('Network.enable'); return {call,close:()=>ws.close()};
}
async function main() {
  const [manifestFile,outputFile] = process.argv.slice(2);
  if(!manifestFile||!outputFile)throw Error('Usage: grazie.cjs MANIFEST.json RAW-RESULTS.json');
  if(fs.existsSync(outputFile))throw Error('Refusing to overwrite evidence');
  const manifest=JSON.parse(fs.readFileSync(manifestFile));
  if(manifest.records.some(r=>/[\r\n]/.test(r.input)))throw Error('Expected unwrapped inputs');
  const base=process.env.CDP_URL||'http://127.0.0.1:9229';
  if(!['127.0.0.1','localhost','[::1]'].includes(new URL(base).hostname))throw Error('Loopback CDP only');
  const targets=await(await fetch(base+'/json/list')).json();
  const drafts=targets.filter(p=>/^chrome-extension:\/\/[^/]+\/draft\/draft.html$/.test(p.url));
  if(drafts.length!==1)throw Error('Expected exactly one official Grazie Text Playground');
  const extensionOrigin=new URL(drafts[0].url).host;
  if(extensionOrigin!=='fonaoompfjljjllgccccgjnhnoghohgc')throw Error('Unrecognized extension');
  const workerTarget=targets.find(p=>p.type==='service_worker'&&new URL(p.url).host===extensionOrigin);
  if(!workerTarget)throw Error('Grazie service worker not active');
  let received=[];
  const worker=await connect(workerTarget,r=>{received.push(r);fs.writeFileSync(outputFile+'.last-response.json',JSON.stringify(received,null,2)+'\n');});
  const draft=await connect(drafts[0],()=>{});
  const evaluate=async expression=>{
    const r=await draft.call('Runtime.evaluate',{expression,returnByValue:true,awaitPromise:true});
    if(r.exceptionDetails)throw Error('Editor evaluation failed');return r.result.value;
  };
  const current=()=>evaluate('document.querySelector("[data-grz-qa=grazie-draft-editor]")?.innerText');
  const set= text=>evaluate(`(()=>{const e=document.querySelector('[data-grz-qa=grazie-draft-editor]');e.focus();document.execCommand('selectAll');document.execCommand(${text?'"insertText",false,'+JSON.stringify(text):'"delete"'});return e.innerText})()`);
  const data={source_sha256:manifest.source_sha256,provider:'Grazie cloud',engine:'Official Grazie extension Text Playground',records:[],omitted:[]};
  const save=()=>fs.writeFileSync(outputFile,JSON.stringify(data,null,2)+'\n');
  let own;
  try {
    if((await current())?.trim()!=='')throw Error('Playground must be empty; refusing to overwrite draft');
    await draft.call('Page.bringToFront');
    for(const record of manifest.records) {
      if(own!==undefined && await current()!==own)throw Error('Draft changed externally');
      received=[];own=record.input;
      if(await set(own)!==own)throw Error('Editor changed input');
      const deadline=Date.now()+15000;let response;
      while(Date.now()<deadline) {
        await delay(500);
        if(await current()!==own)throw Error('Draft changed externally');
        const failed=received.find(r=>r.error||r.status!==200);
        if(failed)throw Error('Cloud response failure: '+JSON.stringify(failed));
        // Sentence sequence must reproduce this exact input (apart from spacing).
        response=received.find(r=>Array.isArray(r.body?.corrections)&&r.body.corrections.map(c=>c.sentence).join(' ').replace(/\s+/g,' ').trim()===editorProse(own).replace(/\s+/g,' ').trim());
        if(response)break;
      }
      if(!response){
        data.omitted.push({id:record.id,reason:'No complete source-matched cloud response',responses:received});save();
        console.error(`Unverified: ${record.id}`);
        if(data.omitted.length>=3)throw Error('Three unverified inputs; inspect service/UI before continuing');
        continue;
      }
      data.records.push({id:record.id,input:own,...response});save();
      console.error(`Collected ${data.records.length}/${manifest.records.length}`);
      await delay(1000);
    }
    data.status='complete';save();
  } catch(e) {data.status=e.message;save();throw e;}
  finally {if(own!==undefined&&await current()===own)await set('');draft.close();worker.close();}
}
if(require.main===module)main().catch(e=>{console.error(e.message);process.exitCode=1});
module.exports={editorProse};
