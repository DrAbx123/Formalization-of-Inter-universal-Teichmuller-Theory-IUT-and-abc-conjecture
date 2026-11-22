import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
function lines(f,a,b){ const t=readFileSync(ROOT+'/'+f,'utf8').split('\n'); return t.slice(a-1,b).map((x,i)=>(a+i)+': '+x).join('\n'); }
console.log('=== FiniteAlignmentSocketInstance 180-205');
console.log(lines('LeanFormal/IUT/IUTIII/Corollary312/StepXI/FiniteAlignmentSocketInstance.lean',180,205));
console.log('=== S650ActualSignedCor312Contract 40-75');
console.log(lines('tmp/sheaf/xif/paper/S650ActualSignedCor312Contract.lean',40,75));
console.log('=== hull log ===');
const hl=ROOT+'/dag/watchdog/logs/tmp_sheaf_xif_paper_Mzk1HullDetStep3115Actual.lean.log';
console.log(existsSync(hl)?readFileSync(hl,'utf8').split('\n').slice(0,6).join('\n'):'no log');
console.log('=== step3115 log ===');
const sl=ROOT+'/dag/watchdog/logs/tmp_sheaf_xif_paper_Mzk1Step3115ComparisonActual.lean.log';
console.log(existsSync(sl)?readFileSync(sl,'utf8').split('\n').slice(0,6).join('\n'):'no log');
console.log('=== files importing V2 or Actual ===');
const all=[];
function walk(d){ for(const e of readdirSync(d,{withFileTypes:true})){ const p=d+'/'+e.name; if(e.isDirectory()){ if(['logs','.lake','.git'].includes(e.name)) continue; walk(p); } else if(e.name.endsWith('.lean')) all.push(p); } }
walk(ROOT+'/tmp/sheaf'); walk(ROOT+'/LeanFormal');
for(const f of all){ if(f.includes('R4LiteralAssemblyV2Actual')||f.includes('R4LiteralAssemblyActual')){ const t=readFileSync(f,'utf8'); if(t.includes('R4LiteralAssemblyV2Actual')&&!f.includes('R4LiteralAssemblyV2Actual')) console.log('  imports V2: '+f.replace(ROOT+'/','')); if(t.includes('R4LiteralAssemblyActual')&&!f.includes('R4LiteralAssemblyActual')) console.log('  imports Actual: '+f.replace(ROOT+'/','')); } }
