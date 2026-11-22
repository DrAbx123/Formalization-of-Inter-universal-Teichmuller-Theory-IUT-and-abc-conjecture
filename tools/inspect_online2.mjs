import { readFileSync, readdirSync } from 'node:fs';
import { join, relative } from 'node:path';
const ROOT='D:/lean';
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git'||x.name==='.tmp-round2-verifier') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
function strip(s){ return s.replace(/\/\-[^-][\s\S]*?-\//g,'').replace(/--[^\n]*/g,'').replace(/"(?:[^"\\]|\\.)*"/g,'""'); }
for(const base of ['tmp/online/Gogopex__iut-lean','tmp/online/Luminescence__IUT']){
  const files=walk(join(ROOT,base),[]);
  let sorry=0; const rows=[];
  for(const f of files){ let s=''; try{s=readFileSync(f,'utf8')}catch{continue} const st=strip(s); const n=(st.match(/\bsorry\b|\badmit\b/g)||[]).length; sorry+=n; if(n) rows.push([relative(join(ROOT,base),f).replace(/\\/g,'/'),n,s.length]); }
  console.log('## '+base+' lean='+files.length+' codeSorry='+sorry);
  for(const r of rows.slice(0,10)) console.log('  sorry',r[0],r[1]);
  const big=files.map(f=>[relative(join(ROOT,base),f).replace(/\\/g,'/'),readFileSync(f,'utf8').length]).sort((a,b)=>b[1]-a[1]).slice(0,12);
  for(const b of big) console.log('  big',b[1],b[0]);
}