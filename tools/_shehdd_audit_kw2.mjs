import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const files=readdirSync(ROOT+'/coord').filter(f=>/^target-chain\.iut-(skeleton|pre-.*)\.json$/.test(f)).sort();
const all=[];
for(const f of files){ const j=JSON.parse(readFileSync(ROOT+'/coord/'+f,'utf8')); for(const n of (j.nodes||[])) all.push({frag:f.replace('target-chain.','').replace('.json',''),id:n.id,kind:n.kind,status:n.status,title:(n.title||''),files:(n.files||[]) }); }
const kw=(s)=>all.filter(n=>(n.id+' '+n.title).toLowerCase().includes(s.toLowerCase()));
for(const s of ['multiradial','Ind1','Ind2','Ind3','indeterminac','procession','label','Kummer isomorphism','q-parameter','qParameter','mono-analytic','log-volume','logVolume','holomorphic hull','possible image','Theorem 3.11','situation']) console.log(s+' -> '+kw(s).length+' :: '+kw(s).slice(0,5).map(n=>n.id).join(','));
