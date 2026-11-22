import { readFileSync, writeFileSync, readdirSync, existsSync, mkdirSync } from 'node:fs';
import { join, relative, dirname } from 'node:path';
const ROOT='D:/lean';
const SRC=join(ROOT,'tmp/external/Takkun-IUT_LEAN');
const DST=join(ROOT,'tmp/sheaf/takkun/IutLean');
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const files=walk(SRC,[]);
// module map: IutLean.X -> tmp.sheaf.takkun.IutLean.X
const out=[];
for(const f of files){ const rel=relative(SRC,f).replace(/\\/g,'/'); if(rel.startsWith('.lake')) continue; const dstRel='tmp/sheaf/takkun/'+rel; const dst=join(ROOT,dstRel); mkdirSync(dirname(dst),{recursive:true}); let s=readFileSync(f,'utf8'); s=s.replace(/^import\s+IutLean\.([A-Za-z0-9_.]+)/gm,'import tmp.sheaf.takkun.IutLean.$1'); writeFileSync(dst,s); out.push(dstRel); }
writeFileSync(join(ROOT,'tmp','takkun_port_list.txt'), out.join('\n')+'\n');
console.log('ported takkun files', out.length);