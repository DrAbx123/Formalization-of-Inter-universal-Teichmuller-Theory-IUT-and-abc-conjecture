import { readFileSync, existsSync, statSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const dag=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const idx=JSON.parse(readFileSync(ROOT+'/coord/repo-route-index-data.json','utf8'));
const lines=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8').split('\n');
const latest=(rel)=>{ for(let i=lines.length-1;i>=0;i--){ if(lines[i].includes('FILE='+rel)) return lines[i]; } return null; };
const oleanFresh=(rel)=>{ const src=ROOT+'/'+rel, ole=ROOT+'/.lake/build/lib/lean/'+rel.replace(/\.lean$/,'.olean'); try{ return existsSync(src)&&existsSync(ole)&&statSync(ole).mtimeMs>=statSync(src).mtimeMs; }catch{ return false; } };
const flattenDecls=(d)=>{ if(!d) return []; if(Array.isArray(d)) return d; const out=[]; for(const [f,ds] of Object.entries(d)){ if(Array.isArray(ds)) for(const x of ds) out.push(f+'::'+x); } return out; };
const idxRows=idx.rows||[];
const objects=[
 {k:'ThetaPilot', label:'Theta-pilot object (IUT III Def 3.8(i))', kws:['thetapilot','theta-pilot','source theta pilot']},
 {k:'QPilot', label:'q-pilot object (Def 3.8(i)); q-parameters (IUT I Def 3.1(b))', kws:['qpilot','q-pilot']},
 {k:'Multiradial', label:'Multiradial representation (Thm 3.11(i))', kws:['multiradial']},
 {k:'Ind1', label:'Indeterminacy Ind1', kws:['ind1']},
 {k:'Ind2', label:'Indeterminacy Ind2', kws:['ind2']},
 {k:'Ind3', label:'Indeterminacy Ind3', kws:['ind3']},
 {k:'HoloHull', label:'Holomorphic hull of possible images (Rmk 3.9.5(i))', kws:['holomorphichull','hull_logvolume','sourceholomorphichull']},
 {k:'LogVolume', label:'Procession-normalized mono-analytic log-volume (Rmk 3.1.1/Prop 3.9)', kws:['logvolume','procession']},
 {k:'KummerIso', label:'Kummer isomorphisms (Thm 3.11(ii))', kws:['kummer','mun']},
 {k:'Labels', label:'Labels 0 / <F_l^#> identification (IUT II Cor 4.10(i))', kws:['thetalink']},
 {k:'HodgeTheater', label:'Hodge theater (IUT I)', kws:['hodge']},
 {k:'Frobenioid', label:'Frobenioid Example 3.6 / model (IUT II)', kws:['frobenioid','example36']},
 {k:'PrimeStrips', label:'F/D prime-strips', kws:['primestrip']},
 {k:'InitialTheta', label:'Initial Theta data / Definition 3.1 clusters', kws:['initialtheta','definition31']},
 {k:'EtTh', label:'Etale theta (EtTh) suite', kws:['etth','etaletheta']},
 {k:'K1K2', label:'Kummer K1/K2 packets', kws:['k1k2']},
 {k:'AbsTopIII', label:'AbsTopIII inputs (Hodge-Arakelov/theta hull, Prop 5.8)', kws:['abstop']},
 {k:'H5', label:'H5 Ox stabilization / hull<=image-volume', kws:['h5','hull09']},
 {k:'H6', label:'H6 geometric core precise input', kws:['h6','geometriccore']},
 {k:'H7Ob9', label:'H7/Ob9 two-sided arbitrary-iterate bound', kws:['h7','ob9','hull13']},
 {k:'GenEll', label:'GenEll (general elliptic) results', kws:['genell']},
 {k:'Belyi', label:'Noncritical Belyi existence / Lemma 2.x inputs', kws:['belyi','lemma24','lemma23']},
 {k:'IUTIVThm110', label:'IUT IV Theorem 1.10 display', kws:['thm110','theorem110','theorem 1.10']},
 {k:'IUTIVSec2', label:'IUT IV Section 2 estimates (arithmetic divisor degree, different, StepV)', kws:['iutiv','section2','arithmeticdivisordegree','stepv','different']},
 {k:'S2717', label:'Cor 3.12 target <=> S2717 upper gap', kws:['s2717','uppergap','papercor312full']},
 {k:'Comparisons', label:'(b)/(c) inputs: undilated height/region bounds', kws:['undilated','regionbound','heightbound','cor312gap']},
 {k:'Them311Assembly', label:'Theorem 3.11 source assembly', kws:['theorem311','thm311']},
 {k:'Cor312Statement', label:'Cor 3.12 conclusion statement (CTheta >= -1)', kws:['cor312','stepxicontract']},
 {k:'Cor312Bridge', label:'Cor312 -> ABC bridge interface / heightBound', kws:['cor312toabcbridge','abcbridgeinterface']},
 {k:'ABCFrontier', label:'ABCFrontier / abc height-weight equivalences', kws:['abcfrontier','abcfrontier','heightweight']},
 {k:'ABCTarget', label:'ABCConjecture final target', kws:['abcconjecture','abctarget']},
 {k:'Section0', label:'Section 0 oriented graphs/saturated path pairs', kws:['section0']},
 {k:'Sources1995', label:'Sources 1995-2015 named input (external theorems)', kws:['sources1995','1995']}
];
const out=[];
for(const o of objects){
  const nodeHits=dag.nodes.filter(n=>{ const s=(n.id+' '+String(n.title||'')+' '+flattenDecls(n.declarations).join(' ')+' '+(n.files||[]).join(' ')).toLowerCase(); return o.kws.some(k=>s.includes(k.toLowerCase())); });
  const fileHits=idxRows.filter(r=>{ const s=(String(r.file||'')+' '+JSON.stringify(r.tags||'')+' '+JSON.stringify(r.decls||'')).toLowerCase(); return o.kws.some(k=>s.includes(k.toLowerCase())); });
  const topNodes=nodeHits.slice(0,4).map(n=>({id:n.id,status:n.status,files:(n.files||[]).slice(0,2),decls:flattenDecls(n.declarations).slice(0,3)}));
  const topFiles=fileHits.slice(0,4).map(r=>({file:r.file,citable:r.citable,evidence:(oleanFresh(r.file)?'olean_fresh':(latest(r.file)||'').slice(0,18))}));
  out.push({key:o.k,label:o.label,nodeHits:nodeHits.length,fileHits:fileHits.length,nodes:topNodes,files:topFiles});
}
writeFileSync(ROOT+'/tmp/_survey_match.json',JSON.stringify(out,null,2));
console.log('written; objects='+out.length);
for(const o of out) console.log(o.key+' | nodes='+o.nodeHits+' files='+o.fileHits+' | '+(o.nodes[0]?o.nodes[0].id+'('+o.nodes[0].status+')':'-')+' | '+(o.files[0]?o.files[0].file.split('/').pop()+'('+o.files[0].citable+'/'+o.files[0].evidence+')':'-'));
