import { readdirSync, readFileSync } from 'node:fs';
const ROOT='D:/lean';
const terms=['Multiradial','multiradial','etHT','EtHT','BPS','HDD','SHE','IPL','APT','qPilot','QPilot','logThetaLattice','LogTheta','ThetaLattice','SourceDTheta','HodgeTheater','Procession','Ind1','Ind2','Ind3','SimultaneousHolomorphic'];
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ const p=d+'/'+x.name; if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const files=walk(ROOT+'/LeanFormal',[]);
const stats={}; for(const t of terms) stats[t]={files:0,decls:0}; const found={};
const declRe=/^\s*(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*(theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+([A-Za-z0-9_'.]+)/gm;
for(const f of files){ let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } for(const t of terms){ if(s.includes(t)){ stats[t].files++; (found[t]=found[t]||new Set()).add(f.replace(ROOT+'/','')); } } }
console.log(JSON.stringify(Object.fromEntries(Object.entries(stats).map(([k,v])=>[k,v.files])),null,1));
for(const t of ['Multiradial','multiradial','etHT','BPS','HDD','SHE','IPL','APT']){ if(found[t]) console.log('## '+t+'\n'+[...found[t]].slice(0,8).join('\n')); }