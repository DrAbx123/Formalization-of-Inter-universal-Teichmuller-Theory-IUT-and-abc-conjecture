import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const dirs=['LeanFormal','tmp/sheaf','tmp/external','logs/upstream','tmp/dsh-oct6-openai-math-survey-20261016/repos/lana','tmp/dsh-oct6-openai-math-survey-20261016/repos'];
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(x.name==='.lake'||x.name==='.git'||x.name==='.lean-shadow'||x.name==='node_modules') continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const files=[]; for(const d of dirs){ walk(join(ROOT,d),files); }
console.log('lean files scanned', files.length);
const groups={
 P1_thm53:['h_non','H_L','Delta_L','rad_L','Theorem53','Thm53','Theorem5_3','TheoremFiveThree','noncritical','Noncritical'],
 P2_data:['compactlyBounded','CBS','U_X','K_V','Exc','h_d','kappa_log','kappaLog','kappaPrm','552960','deltaPrm'],
 P3_thm54:['Theorem54','Thm54','Theorem5_4','Claims5_4','claim54','cubeStep','Thm54Shape'],
 P4_sharp:['1.022','0.00071','1.00072','Rosser','Schoenfeld','Mihailescu','MihailescuRassias','nthPrime','PrimeCounting']
};
const hits={}; for(const g of Object.keys(groups)) hits[g]=[];
for(const f of files){ let s=''; try{ const st=1; s=readFileSync(f,'utf8'); }catch{ continue; } for(const [g,terms] of Object.entries(groups)){ if(terms.some(t=>s.includes(t))){ if(hits[g].length<60) hits[g].push(f.replace(ROOT+'/','')); } } }
for(const [g,list] of Object.entries(hits)){ console.log('##',g,'files',list.length); for(const f of list.slice(0,20)) console.log(' ',f); }