import { readFileSync, readdirSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const audit=JSON.parse(readFileSync(ROOT+'/tmp/_probe_audit_rows.json','utf8'));
const stems=audit.map(r=>r.stem);
const restored=['_AutoProbe_Mzk1StepVPaperActual','_AutoProbe_Mzk1Cor312TargetWiringActual','_AutoProbe_Mzk1IUTIIILinkActual','_AutoProbe_Mzk1KummerThetaInterfaceActual','_AutoProbe_Mzk1G2CDConsumerActual','_AutoProbe_Mzk1R9PointMembershipConsumerActual','_AutoProbe_Mzk1GeomCoreFiniteMapChartInterfaceActual','_AutoProbe_Mzk1GeomCoreLineBundleInterfaceActual','_AutoProbe_Mzk1Thm110SlackActual','_AutoProbe_Mzk1E5UniformHeightActual','_AutoProbe_Mzk1Prop58iConcreteActual','_AutoProbe_Mzk1StepXIContractConstructionActual','_AutoProbe_Mzk1Cor312ObligationConsumerActual','_AutoProbe_Mzk1R9HullConsumerActual','_AutoProbe_Hull13TwoSidedBoundActual','_AutoProbe_AbsTopIII05Section0ObjectsActual'];
const files=[];
for(const d of ['coord','dag']){ const walk=(rel)=>{ let ents; try{ ents=readdirSync(ROOT+'/'+rel,{withFileTypes:true}); }catch{ return; } for(const e of ents){ const p=rel+'/'+e.name; if(e.isDirectory()){ if(/node_modules|\.lake|generated/.test(p)) continue; walk(p); } else if(/\.(json|md|txt)$/.test(e.name)||e.name==='target-chain.json') files.push(p); } }; walk(d); }
const hits=[];
for(const f of files){ let txt; try{ txt=readFileSync(ROOT+'/'+f,'utf8'); }catch{ continue; } for(const s of [...stems,...restored]){ if(txt.includes(s)){ hits.push({file:f, needle:s}); } } }
console.log('files scanned='+files.length+' hits='+hits.length);
for(const h of hits.slice(0,40)) console.log(h.file+' :: '+h.needle);
