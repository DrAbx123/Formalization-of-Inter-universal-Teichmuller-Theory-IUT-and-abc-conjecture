import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
function strip(s){ return s.replace(/\/\-[^-][\s\S]*?-\//g,'').replace(/\/\-.*?-\//g,'').replace(/--[^\n]*/g,'').replace(/"(?:[^"\\]|\\.)*"/g,'""'); }
for(const base of ['tmp/external/Takkun-IUT_LEAN','tmp/external/promachina-iut-lean-latest','tmp/external/promachina-iut-lean']){
 const files=walk(join(ROOT,base),[]); let total=0; const hits=[];
 for(const f of files){ let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } const st=strip(s); const n=(st.match(/\bsorry\b|\badmit\b/g)||[]).length; if(n){ total+=n; hits.push([f.replace(ROOT+'/',''),n]); } }
 console.log(base+' files='+files.length+' codeSorry='+total+' inFiles='+hits.length);
 for(const [f,n] of hits.slice(0,10)) console.log('  '+f+' : '+n);
}