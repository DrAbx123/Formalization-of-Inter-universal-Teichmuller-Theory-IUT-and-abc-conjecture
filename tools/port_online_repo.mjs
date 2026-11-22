import { readFileSync, writeFileSync, readdirSync, existsSync, mkdirSync } from 'node:fs';
import { join, relative, dirname } from 'node:path';
const ROOT='D:/lean';
const [srcRel,dstRel,modRoot]=process.argv.slice(2);
if(!srcRel||!dstRel||!modRoot){ console.log('usage: node tools/port_online_repo.mjs <srcdir> <dstdir> <ModuleRoot>'); process.exit(1); }
const SRC=join(ROOT,srcRel), DST=join(ROOT,dstRel);
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const files=walk(SRC,[]);
const out=[];
for(const f of files){ const rel=relative(SRC,f).replace(/\\/g,'/'); const dst=join(DST,rel); mkdirSync(dirname(dst),{recursive:true}); let s=readFileSync(f,'utf8'); s=s.replace(new RegExp('^import\\s+'+modRoot+'\\.','gm'),'import '+(dstRel.replace(/\//g,'.')+'.'+modRoot)+'.'); s=s.replace(new RegExp('^public import\\s+'+modRoot+'\\.','gm'),'import '+(dstRel.replace(/\//g,'.')+'.'+modRoot)+'.'); writeFileSync(dst,s); out.push(dstRel.replace(/\\/g,'/')+'/'+rel); }
writeFileSync(join(ROOT,'tmp','port_'+modRoot+'_list.txt'), out.join('\n')+'\n');
console.log('ported',out.length,'files to',dstRel);