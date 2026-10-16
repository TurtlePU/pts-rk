// Offline protocol test. No request reaches DeepL or an authenticated browser.
const assert=require('assert'),http=require('http'),fs=require('fs'),os=require('os'),path=require('path');
const {spawn}=require('child_process');const {WebSocketServer}=require('ws');
async function run(draft){
 const temp=fs.mkdtempSync(path.join(os.tmpdir(),'prose-review-test-'));
 const input='We need info for PROTECTED1X1.';
 const manifest={source_sha256:'fixture',records:[{id:'L1',line:1,end_line:1,source:'We need info for $x$.',input,mapping:{PROTECTED1X1:'$x$'}}]};
 fs.writeFileSync(path.join(temp,'manifest.json'),JSON.stringify(manifest));
 let current=draft,inserted=[];
 const server=http.createServer((req,res)=>{
  assert.equal(req.url,'/json/list');res.setHeader('Content-Type','application/json');
  res.end(JSON.stringify([{type:'page',url:'https://www.deepl.com/en/write',webSocketDebuggerUrl:`ws://127.0.0.1:${server.address().port}/ws`}]));
 });
 const wss=new WebSocketServer({server});
 wss.on('connection',ws=>ws.on('message',raw=>{
  const m=JSON.parse(raw);assert.equal(m.method,'Runtime.evaluate');const e=m.params.expression;
  let value;
  if(e.includes("execCommand('insertText'")){
   const match=e.match(/insertText',false,("(?:[^"\\]|\\.)*")\)/);assert(match);
   current=JSON.parse(match[1]);inserted.push(current);value=current;
  }else if(e.startsWith('({source:')){value={source:current,result:current.replace('info','information'),text:'DeepL Write'};
  }else if(e.includes('document.body.innerText')){value='English (British)';
  }else if(e.includes('write-results-heading')){value=current.replace('info','information');
  }else{value=current}
  ws.send(JSON.stringify({id:m.id,result:{result:{type:typeof value,value}}}));
 }));
 await new Promise(r=>server.listen(0,'127.0.0.1',r));
 const child=spawn(process.execPath,[path.join(__dirname,'../scripts/deepl.cjs'),path.join(temp,'manifest.json'),path.join(temp,'results.json')],{env:{...process.env,CDP_URL:`http://127.0.0.1:${server.address().port}`}});
 let errors='';child.stderr.on('data',d=>errors+=d);
 const code=await new Promise(r=>child.on('exit',r));
 if(draft){assert.notEqual(code,0);assert.equal(current,draft);assert.equal(inserted.length,0);assert(!fs.existsSync(path.join(temp,'results.json')));
 }else{
  assert.equal(code,0,errors);const result=JSON.parse(fs.readFileSync(path.join(temp,'results.json')));
  assert.equal(result.records[0].output,'We need information for PROTECTED1X1.');
  assert.equal(current,'');assert(inserted.every(s=>!s.includes('$')));
 }
 await new Promise(r=>wss.close(r));await new Promise(r=>server.close(r));
 console.log(draft?'Existing draft protected':'Protected-input collection and cleanup passed');
}
(async()=>{await run('');await run('A user draft.');})().catch(e=>{console.error(e);process.exit(1)});
