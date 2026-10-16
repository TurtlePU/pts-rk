#!/usr/bin/env node
// Operate only on a dedicated, user-exposed DeepL tab. Never read credentials.
const fs = require('fs');
const WebSocket = require('ws');
const pause = ms => new Promise(resolve => setTimeout(resolve, ms));
async function main() {
  const [manifestFile, outputFile] = process.argv.slice(2);
  if (!manifestFile || !outputFile) throw Error('Usage: deepl.cjs MANIFEST.json OUTPUT.json');
  if (fs.existsSync(outputFile)) throw Error('Refusing to overwrite results');
  const manifest = JSON.parse(fs.readFileSync(manifestFile));
  if (manifest.records.some(r => r.input.length > 1400 || /[\r\n]/.test(r.input))) {
    throw Error('Inputs must be single unwrapped paragraphs <= 1400 characters');
  }
  const base = process.env.CDP_URL || 'http://127.0.0.1:9228';
  if (!['localhost','127.0.0.1','[::1]'].includes(new URL(base).hostname)) {
    throw Error('Only an explicitly exposed loopback CDP session is supported');
  }
  const pages = await (await fetch(base + '/json/list')).json();
  const eligible = pages.filter(p => p.type === 'page' && /^https:\/\/www\.deepl\.com\/(?:[a-z-]+\/)?write(?:[/#?]|$)/.test(p.url));
  if (eligible.length !== 1) throw Error('Expected exactly one dedicated DeepL Write tab');
  const ws = new WebSocket(eligible[0].webSocketDebuggerUrl);
  await new Promise((resolve,reject)=>{ws.once('open',resolve);ws.once('error',reject)});
  let id = 0; const pending = new Map();
  ws.on('message',raw=>{const m=JSON.parse(raw);if(pending.has(m.id)){pending.get(m.id)(m);pending.delete(m.id)}});
  const call = (method,params) => new Promise((resolve,reject)=>{
    const timer=setTimeout(()=>reject(Error('CDP request timeout')),10000);
    pending.set(++id,m=>{clearTimeout(timer);resolve(m)});ws.send(JSON.stringify({id,method,params}));
  });
  const evaluate = async expression => {
    const r=await call('Runtime.evaluate',{expression,returnByValue:true,awaitPromise:true});
    if (r.error || r.result.exceptionDetails) throw Error('Editor evaluation failed');
    return r.result.result.value;
  };
  const sourceSelector='[aria-labelledby=write-source-heading]';
  const resultSelector='[aria-labelledby=write-results-heading]';
  const setInput=async text=>evaluate(`(()=>{const e=document.querySelector(${JSON.stringify(sourceSelector)});if(!e)throw Error('Missing source');e.focus();document.execCommand('selectAll');document.execCommand('insertText',false,${JSON.stringify(text)});return e.innerText})()`);
  const data={source_sha256:manifest.source_sha256,provider:'DeepL Write',records:[]};
  let ownsInput=false;
  try {
    const initial=await evaluate(`document.querySelector(${JSON.stringify(sourceSelector)})?.innerText`);
    if(initial===undefined || initial.trim())throw Error('Source editor must exist and be empty');
    data.engine=await evaluate('document.body.innerText.slice(0,1500)');
    for(const record of manifest.records){
      const old=await evaluate(`document.querySelector(${JSON.stringify(resultSelector)})?.innerText`);
      ownsInput=true;
      if(await setInput(record.input)!==record.input)throw Error('Editor altered/truncated input');
      const keys=new Set(record.input.match(/(?:MATH|REF|PROTECTED)\d+X\d+/g)||[]);
      let previous='',stable=0,result='';const deadline=Date.now()+45000;
      while(Date.now()<deadline){
        await pause(500);
        const state=await evaluate(`({source:document.querySelector(${JSON.stringify(sourceSelector)})?.innerText,result:document.querySelector(${JSON.stringify(resultSelector)})?.innerText,text:document.body.innerText.slice(0,6000)})`);
        if(state.source!==record.input)throw Error('Source changed externally; stopping');
        if(/too many requests|limit reached|temporarily blocked|sign in to continue/i.test(state.text))throw Error('Authentication/quota/service limit; stopping');
        const now=(state.result||'').trim();
        const found=now.match(/(?:MATH|REF|PROTECTED)\d+X\d+/g)||[];
        // Never mistake a late result for the previous source for this result.
        const current=found.every(k=>keys.has(k))&&(!keys.size||found.some(k=>keys.has(k)));
        stable=now&&now!==old&&now===previous&&current?stable+1:0;previous=now;
        if(stable>=6){result=now;break}
      }
      if(!result)throw Error('No stable source-matched result; inspect the current editor, do not guess');
      data.records.push({...record,provider:data.provider,output:result});
      fs.writeFileSync(outputFile,JSON.stringify(data,null,2)+'\n');
      console.error(`Collected ${data.records.length}/${manifest.records.length}`);
    }
  } finally {
    // Do not clear an editor changed externally while this tool was running.
    if(ownsInput){
      const current=await evaluate(`document.querySelector(${JSON.stringify(sourceSelector)})?.innerText`);
      if(manifest.records.some(r=>r.input===current))await setInput('');
    }
    ws.close();
  }
}
main().catch(e=>{console.error(e.message);process.exitCode=1});
