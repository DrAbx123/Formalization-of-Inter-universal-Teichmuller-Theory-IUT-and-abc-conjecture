import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const skip=new Set(['.lake','.git','.lean-shadow','node_modules','.elan','.cache']);
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ if(skip.has(x.name)) continue; const p=join(d,x.name); if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const dirs=['LeanFormal','tmp/sheaf','tmp/external','logs/upstream','tmp/dsh-oct6-openai-math-survey-20261016/repos'];
let files=[]; for(const d of dirs) walk(join(ROOT,d),files);
console.log('files',files.length);
const pats=[
 ['ThetaLink',/\b(ThetaLink|ThetaLogLink|ThetaLinkData|thetaLink)\b/],
 ['LogLink',/\b(LogLink|LogLinkData|logLink)\b/],
 ['D-Layer',/\b(DGreater|DLess|DPlus|DMinus|D_'|DData|HodgeTheaterD)\b/],
 ['ellNF',/\b(ellNF|EllNF|lNF|ellNf|EllNf)\b/],
 ['Ind123',/\b(Ind1|Ind2|Ind3)\b/],
 ['MultiradialAlg',/\b(Multiradial|multiradial)\b/],
 ['ThetaPilotSrc',/\b(ThetaPilotSource|thetaPilotSource|GlobalThetaPilot|globalThetaPilot|ThetaPilotObject)\b/],
 ['GlobalQPilot',/\b(GlobalQPilot|globalQPilot|qPilotGlobal)\b/],
 ['HullFiniteness',/\b(HullFiniteness|hullFiniteness|IQHullFiniteness|globalIQHull)\b/],
 ['LogShell',/\b(LogShell|logShell|LogShellFamily)\b/]
];
const stats={}; for(const [n] of pats) stats[n]={deflike:[],hits:0};
for(const f of files){ let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } const rel=f.replace(ROOT+'/',''); const lines=s.split(/\r?\n/);
 for(const [n,re] of pats){ if(!re.test(s)) continue; stats[n].hits++;
  for(let i=0;i<lines.length;i++){ const L=lines[i]; if(re.test(L) && /^(structure|def|abbrev|class|inductive|theorem)\s+/.test(L)){ if(stats[n].deflike.length<80) stats[n].deflike.push(rel+':'+(i+1)+': '+L.trim().slice(0,150)); } }
 }
}
for(const [n] of pats){ console.log('## '+n+' files='+stats[n].hits+' deflike='+stats[n].deflike.length); for(const d of stats[n].deflike.slice(0,12)) console.log('  '+d); }