import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const names=['_AutoProbe_Mzk1StepVPaperActual','_AutoProbe_Mzk1Cor312TargetWiringActual','_AutoProbe_Mzk1IUTIIILinkActual','_AutoProbe_Mzk1KummerThetaInterfaceActual','_AutoProbe_Mzk1G2CDConsumerActual','_AutoProbe_Mzk1R9PointMembershipConsumerActual','_AutoProbe_Mzk1GeomCoreFiniteMapChartInterfaceActual','_AutoProbe_Mzk1GeomCoreLineBundleInterfaceActual','_AutoProbe_Mzk1Thm110SlackActual','_AutoProbe_Mzk1E5UniformHeightActual','_AutoProbe_Mzk1Prop58iConcreteActual','_AutoProbe_Mzk1StepXIContractConstructionActual','_AutoProbe_Mzk1Cor312ObligationConsumerActual','_AutoProbe_Mzk1R9HullConsumerActual','_AutoProbe_Hull13TwoSidedBoundActual','_AutoProbe_AbsTopIII05Section0ObjectsActual'];
const lines=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const latest=(rel)=>{ for(let i=lines.length-1;i>=0;i--){ if(lines[i].includes('FILE='+rel)) return lines[i]; } return null; };
const st={}; let ok=0, pending=0;
for(const n of names){ const lr=latest('tmp/sheaf/xif/paper/'+n+'.lean'); if(!lr) { st[n]='pending'; pending++; } else if(lr.includes('EXIT=0')) { st[n]='EXIT0'; ok++; } else { st[n]='EXIT1'; } }
const p=ROOT+'/coord/PROBE-AUDIT.md';
let txt=readFileSync(p,'utf8');
const add='\n## Verification of rebuilt probes\n\n- Rebuilt 16 AutoProbes: EXIT0='+ok+', pending='+pending+', EXIT1='+(16-ok-pending)+'.\n'+
Object.entries(st).map(([k,v])=>'- '+k+': '+v).join('\n')+'\n';
if(!txt.includes('## Verification of rebuilt probes')) txt+=add;
writeFileSync(p,txt);
console.log('audit verification appended: EXIT0='+ok+' pending='+pending);
