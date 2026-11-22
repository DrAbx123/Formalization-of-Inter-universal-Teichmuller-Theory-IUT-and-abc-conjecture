import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const base=join(ROOT,'tmp/sheaf/lana/iut');
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const files=walk(base,[]);
const terms=['Cor312VariantHolds','Cor312Variant','Corollary312Variant','abc_of_cor312Variant','variantHolds'];
for(const f of files){ let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } for(const t of terms){ if(s.includes(t)){ const rel=f.replace(ROOT+'/',''); const lines=s.split(/\r?\n/); const hits=lines.map((l,i)=>[i+1,l]).filter(([i,l])=>l.includes(t)); for(const [i,l] of hits.slice(0,4)) console.log(t,'|',rel+':'+i,'|',l.trim().slice(0,160)); } } }