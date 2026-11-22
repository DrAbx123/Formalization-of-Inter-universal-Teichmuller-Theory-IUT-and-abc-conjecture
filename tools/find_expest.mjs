import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
const terms=['ExpEst','explicit','Explicit','Chebyshev','PrimeCounting','primeCounting','nthPrime','NthPrime','thetaCheb','Cheb','Hunif','Kappa','kappa','logCond','logDiff','MonoComplex','monoComplex','Mu6','mu6','PetRequirement'];
for(const t of terms){ const hits=idx.filter(d=>d.name.includes(t)); if(hits.length){ console.log('##',t,hits.length); for(const h of hits.slice(0,10)) console.log(' ',h.kind,h.name,'@',h.file); } }
console.log('--- files with ExpEst/Explicit in path ---');
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ const p=d+'/'+x.name; if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const files=walk(ROOT+'/LeanFormal',[]).concat(walk(ROOT+'/tmp/sheaf/xif/paper',[]));
const fl=files.filter(f=>/ExpEst|Explicit|Estimate/i.test(f)); console.log(fl.map(f=>f.replace(ROOT+'/','')).slice(0,40).join('\n'));