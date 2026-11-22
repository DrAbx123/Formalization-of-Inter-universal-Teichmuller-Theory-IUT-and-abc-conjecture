import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const txt=readFileSync(ROOT+'/dag/THEOREM-DAG.md','utf8');
const lines=txt.split('\n').filter(l=>l.startsWith('| '));
const rows=lines.slice(1).map(l=>{ const c=l.split('|').map(x=>x.trim()); return {id:c[1],status:c[2],decls:c[3]}; }).filter(r=>r.id);
const kws=['cor312','Cor312','thm311','Theorem311','stepxi','StepXI','hodge','Hodge','frobenioid','Frobenioid','etth','EtTh','logshell','LogShell','kummer','Kummer','theta','Theta','absTop','AbsTop','hull','Hull','genell','GenEll','belyi','Belyi','iutiv','IUTIV','section0','Section0','qpilot','QPilot','prime','Prime','ind1','Ind1','ind2','Ind2','ind3','Ind3','multiradial','Multiradial','h6','H6','h5','H5','ob9','Ob9','source','Source','initial','Initial'];
const hits=new Map();
for(const kw of kws){ for(const r of rows){ if((r.id+' '+r.decls).toLowerCase().includes(kw.toLowerCase())){ hits.set(r.id,r); } } }
console.log('theorem-dag rows='+rows.length+' matched unique='+hits.size);
for(const [id,r] of [...hits].slice(0,120)) console.log(id+' | '+r.status+' | '+r.decls.slice(0,150));
