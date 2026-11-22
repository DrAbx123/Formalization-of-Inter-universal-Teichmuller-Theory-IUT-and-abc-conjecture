import { readFileSync, readdirSync, existsSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const groups = {
 R1_multiradial:['Multiradial','multiradial','FiniteMultiradial','ColumnCarrier','DTheta','H1H2'],
 R2_descent:['Ind1','Ind2','Ind3','Indeterminacy','Descent','descent','Coricity','coricity'],
 R3_literal_IQ:['GlobalIQ','globalIQ','LiteralIQ','literalIQ','IQCarrier','IQHull','Haar','Compact','compact'],
 R4_four_triangles:['FourTriangle','HDD','HullDeterminant','SHE','simultaneous','Simultaneous','APT','IPL','StepXIContract'],
 fixed_beta:['fixedBeta','FixedBeta','Avoidance','avoidance'],
 scheme_side:['schemeSide','SchemeSide','sectionMap','placePoint'],
 fiber_functor:['FiberFunctor','fiberFunctor','GaloisCategory','PreGaloisCategory'],
 qpilot:['QPilot','qPilot','qpilot','ThetaPilot','thetaPilot'],
 iut4_compare:['IUTIVSection2','Section2Uniform','Comparison','comparison','StepV','Estimates']
};
const declIndex=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8'));
const decls=declIndex.declarations||[];
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ const p=d+'/'+x.name; if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const files=walk(ROOT+'/LeanFormal',[]).concat(walk(ROOT+'/tmp/sheaf',[]));
const oleanOf=(f)=>{ const rel=f.replace(ROOT+'/','').replace(/\.lean$/,''); return existsSync(ROOT+'/.lake/build/lib/lean/'+rel+'.olean'); };
const result={generated_at:new Date().toISOString(), groups:{}};
for(const [g,terms] of Object.entries(groups)){
  const declHits=[];
  for(const d of decls){ if(terms.some(t=>d.name.includes(t))){ declHits.push({name:d.name,file:d.file,kind:d.kind}); if(declHits.length>400) break; } }
  const fileHits=[];
  for(const f of files){ let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } if(terms.some(t=>s.includes(t))){ const rel=f.replace(ROOT+'/',''); fileHits.push({file:rel,olean:oleanOf(f)}); if(fileHits.length>400) break; } }
  const summary={terms, decls:declHits.length, files:fileHits.length, files_with_olean:fileHits.filter(x=>x.olean).length};
  result.groups[g]={summary, decl_sample:declHits.slice(0,25), file_sample:fileHits.filter(x=>x.olean).slice(0,15), files_no_olean:fileHits.filter(x=>!x.olean).slice(0,10)};
  console.log(g, JSON.stringify(summary));
}
writeFileSync(ROOT+'/dag/GAP-CLOSURE-CANDIDATES.json', JSON.stringify(result,null,2));
const md=['# GAP CLOSURE CANDIDATES (A483): exhaustive repo search per gap','', 'generated: '+result.generated_at,''];
for(const [g,v] of Object.entries(result.groups)){ md.push('## '+g,'','terms: `'+v.summary.terms.join(', ')+'`','','| metric | value |','|---|---|','| declaration hits | '+v.summary.decls+' |','| file hits | '+v.summary.files+' |','| file hits with olean | '+v.summary.files_with_olean+' |',''); md.push('### sample declarations',''); for(const d of v.decl_sample) md.push('- `'+d.name+'` ('+d.kind+') in `'+d.file+'`'); md.push(''); md.push('### sample compiled files',''); for(const f of v.file_sample.slice(0,10)) md.push('- `'+f.file+'`'); md.push(''); }
writeFileSync(ROOT+'/coord/GAP-CLOSURE-A483.md', md.join('\n'));
console.log('done');