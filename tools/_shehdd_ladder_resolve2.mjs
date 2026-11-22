import { readFileSync, existsSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
function walk(dir,acc){ for(const e of readdirSync(dir,{withFileTypes:true})){ const p=join(dir,e.name); if(e.isDirectory()){ if(['logs','.lake','.git','vendor','external'].includes(e.name)) continue; walk(p,acc); } else if(e.name.endsWith('.lean')) acc.push(p.replace(ROOT+'/','').replace(/\\/g,'/')); } return acc; }
const files=walk(ROOT+'/LeanFormal',[]).concat(walk(ROOT+'/tmp/sheaf',[]));
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
const declsByFile={}; for(const d of idx){ if(d.file) (declsByFile[d.file]=declsByFile[d.file]||[]).push(d.name); }
const groups={
 'R1 BPS->mlt.rep': ['SourceLogShellCarrier','PrimeStripsConstruction','SourceHodgeTheater','SourceDThetaConstruction','SourceH1H2Construction','MultiradialAlgorithmReduction','SourceFiniteMultiradial'],
 'R2 dsc': ['Ind1Reduction','Ind2Reduction','K1K2BoundaryReduction','SourceColumnCarrierIdentification','SourceProcessionStepXI','SourceAdjacentColumnProcessionIsomorphism'],
 'R3 hull+det': ['HullDeterminantLogVolumeReduction','PaperIQCarrierActual','S2723GlobalIQHullActual','S3129IQHullLogVolumeSourceActual'],
 'R4 HDD.SHE': ['ArithmeticQPilot','CardHullRealGeometryGapCards','S1929LiteralIQCarrierActual','SourceSHETransportObligations','Obligations','APT','CertificateHullWiring','ConcreteFiniteRouteColumns','StepXIContract']
};
for(const [g,tokens] of Object.entries(groups)){
  console.log('## '+g);
  for(const tok of tokens){
    const fileHits=files.filter(f=>f.split('/').pop().replace(/\.lean$/,'').toLowerCase().includes(tok.toLowerCase())).slice(0,4);
    const declHits=idx.filter(d=>(d.name===tok)||d.name.endsWith('.'+tok)).slice(0,4);
    console.log('TOKEN '+tok+' files='+fileHits.length+' decls='+declHits.length);
    for(const f of fileHits){ const ds=declsByFile[f]||[]; console.log('  FILE '+f+' olean='+olean(f)+' nd='+ds.length+' e.g. '+ds.slice(0,3).join(',')); }
    for(const d of declHits) console.log('  DECL '+d.name+' @ '+d.file+':'+(d.line||''));
  }
}
