import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ const p=d+'/'+x.name; if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const files=walk(ROOT+'/LeanFormal',[]).concat(walk(ROOT+'/tmp/sheaf/xif/paper',[]));
const re=/theorem\s+([A-Za-z0-9_'.]+)\s*([^:]*?):\s*Cor312Conclusion\b/g;
const out=[];
for(const f of files){ let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } let m; re.lastIndex=0; while((m=re.exec(s))){ out.push({file:f.replace(ROOT+'/',''),name:m[1],binder:m[2].replace(/\s+/g,' ').slice(0,120)}); } }
console.log('candidates',out.length);
for(const c of out.slice(0,80)) console.log(c.name,'|',c.binder,'|',c.file);