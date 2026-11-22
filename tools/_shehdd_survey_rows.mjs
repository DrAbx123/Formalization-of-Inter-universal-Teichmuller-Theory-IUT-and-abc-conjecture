import { readFileSync, existsSync, statSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const dag=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const idx=JSON.parse(readFileSync(ROOT+'/coord/repo-route-index-data.json','utf8'));
const idxRows=idx.rows||[];
const lines=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const latest=(rel)=>{ for(let i=lines.length-1;i>=0;i--){ if(lines[i].includes('FILE='+rel)) return lines[i]; } return null; };
const oleanFresh=(rel)=>{ const src=ROOT+'/'+rel, ole=ROOT+'/.lake/build/lib/lean/'+rel.replace(/\.lean$/,'.olean'); try{ return existsSync(src)&&existsSync(ole)&&statSync(ole).mtimeMs>=statSync(src).mtimeMs; }catch{ return false; } };
const flat=(n)=>{ const d=n.declarations; if(!d) return []; if(Array.isArray(d)) return d; const out=[]; for(const [f,ds] of Object.entries(d)){ if(Array.isArray(ds)) for(const x of ds) out.push({file:f,decl:x}); } return out; };
const byId=(id)=>dag.nodes.find(n=>n.id===id);
const chosen={
 ThetaPilot:['e-deep:E2.hullClosureLaws'],
 QPilot:['iut-skeleton:QPilot','iut-pre-abc:QPilot'],
 Multiradial:['iut-skeleton:Thm311','iutiii:IUTIII.THM311.OUTPUT_ALGORITHM'],
 Ind1:['iut-skeleton:Ind1','iutiii:IUTIII.IND1'],
 Ind2:['iut-skeleton:Ind2','iutiii:IUTIII.IND2'],
 Ind3:['iut-skeleton:Ind3','iutiii:IUTIII.IND3'],
 HoloHull:['iutiii:IUTIII.HULL.CARD_GEOMETRY','e-deep:E5.srcUnitRegion'],
 LogVolume:['e-deep:E5.comparisonGaps','iutiii:IUTIII.HULL.DET_LOG_VOLUME'],
 KummerIso:['iutiii:IUTIII.STEPXI.LOGSHELL_MUN','e-deep:E1.logShellBridge'],
 Labels:['iut-pre-abc:FrobeniusPicture.graph'],
 HodgeTheater:['iut-pre-abc:HodgeTheater.core','iut-pre-abc:HodgeTheater.family'],
 Frobenioid:['iut-pre-abc:Frobenioid.Example36','e-deep:E4.example36'],
 PrimeStrips:['iut-pre-abc:PrimeStrips.FD'],
 InitialTheta:['e-deep:iuti-source-def31-dual-alignment','iut-pre-abc:InitialTheta.data'],
 EtTh:['e-deep:E4.etthConsumer'],
 K1K2:['iut-skeleton:K1K2'],
 AbsTopIII:['e-deep:E1.absTopIII05Refined','e-deep:E1.absTopIII05Inputs'],
 H5:['e-deep:E2.H5framing','e-deep:E2.h5Gap'],
 H6:['e-deep:E1.absTopIII05Inputs'],
 H7Ob9:['e-deep:E3.oneSided','e-deep:E3.twoSided','e-deep:E3.deepOb9'],
 GenEll:['e-deep:E2.hullClosureLaws'],
 Belyi:['B1-fold','B5-lemma23-moebius'],
 IUTIVThm110:['e-deep:E5.display'],
 IUTIVSec2:['T4-iut4-arithmetic-degree'],
 S2717:['e-deep:E5.s2717'],
 Comparisons:['T1-cor312-abc-bridge','e-deep:E5.comparisonGaps'],
 Them311Assembly:['iut-skeleton:Thm311','routes:theorem311_assembly'],
 Cor312Statement:['iutiii:IUTIII.COR312.TARGET','iut-skeleton:Cor312'],
 Cor312Bridge:['T1-cor312-abc-bridge'],
 ABCFrontier:['T3-abc-frontier'],
 ABCTarget:['T0-abc-target'],
 Section0:['iut-pre-abc:Section0.paths'],
 Sources1995:['iut-skeleton:Sources1995_2015']
};
const rows=[];
for(const [obj,ids] of Object.entries(chosen)){
  for(const id of ids){
    const n=byId(id); if(!n){ rows.push({obj,id,missing:true}); continue; }
    const decls=flat(n).slice(0,4);
    const files=(n.files||[]).slice(0,3);
    const ev=files.map(f=>({file:f,olean:oleanFresh(f),last:(latest(f)||'').slice(0,40),row:(idxRows.find(r=>r.file===f)||{}).citable||'-'}));
    rows.push({obj,id,status:n.status,kind:n.kind,title:(n.title||'').slice(0,80),decls,files,ev});
  }
}
writeFileSync(ROOT+'/tmp/_survey_rows.json',JSON.stringify(rows,null,2));
console.log('rows='+rows.length+' missing='+rows.filter(r=>r.missing).length);
for(const r of rows.slice(0,20)) console.log(r.obj+' | '+r.id+' | '+(r.missing?'MISSING':r.status)+' | decls='+(r.decls?r.decls.length:0)+' files='+(r.files?r.files.length:0));
