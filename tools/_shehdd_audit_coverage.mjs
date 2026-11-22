import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const files=readdirSync(ROOT+'/coord').filter(f=>/^target-chain\.iut-(skeleton|pre-.*)\.json$/.test(f)).sort();
const all=[];
for(const f of files){ const j=JSON.parse(readFileSync(ROOT+'/coord/'+f,'utf8')); for(const n of (j.nodes||[])) all.push({frag:f.replace('target-chain.','').replace('.json',''),id:n.id,kind:n.kind,status:n.status,title:(n.title||'').slice(0,80),files:(n.files||[]).length}); }
console.log('total='+all.length);
const kw=(s)=>all.filter(n=>(n.id+' '+n.title).toLowerCase().includes(s.toLowerCase()));
for(const s of ['Hodge','Frobenioid','EtTh','EtaleTheta','LogShell','Kummer','MuN','ThetaPilot','PrimeStrip','AbsTop','Hull','H5','H6','H7','Ob9','GenEll','IUTIV','Section1','Theorem311','Cor312','Cor 3.12','StepXI','QPilot','FrobeniusPicture','InitialTheta','Section0','Belyi','Height','Weight']) console.log(s+' -> '+kw(s).length+' :: '+kw(s).map(n=>n.id).slice(0,6).join(','));
