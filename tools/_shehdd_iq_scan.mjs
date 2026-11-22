import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
const groups=[
 ['IQ carrier / paper-shaped', /IQCarrier|IQHull|IQ\(|vdash|SourceImageRealization|SourceUnitRegionHaarData|IQHullLogVolumeInterface/],
 ['log-shell', /logShell|LogShell|integralLogShell/],
 ['Haar measure', /Haar|haar/],
 ['restricted product / tensor', /RestrictedProduct|restrictedProduct|TensorPacket|tensorPacket|PositivePacket|QVFamTensor|TensorTuple/],
 ['compactness / finite hull', /CompactSpace|IsCompact|ProperSpace|sourceHull|FiniteHull|hullVolume/],
 ['theta-pilot image', /ThetaPilotObject|possibleImage|PossibleImage|possibleThetaPilotImageSet|sourceMultiradialPossibleImage|sourceMultiradialMap/]
];
for(const [label,re] of groups){
  const hits=idx.filter(d=>re.test(d.name)||re.test(d.file||''));
  const byFile={}; for(const h of hits){ byFile[h.file]=(byFile[h.file]||0)+1; }
  const top=Object.entries(byFile).sort((a,b)=>b[1]-a[1]).slice(0,16);
  console.log('=== '+label+' hits='+hits.length);
  for(const [f,c] of top) console.log('  '+f+' ('+c+')');
}
const sh=idx.filter(d=>/SourceHullInterfaceDischarge/.test(d.file||''));
const shFiles=[...new Set(sh.map(d=>d.file))];
console.log('SourceHullInterfaceDischarge decls='+sh.length+' files='+shFiles.join(','));
for(const d of sh.slice(0,14)) console.log('   '+d.name+' | '+d.file+':'+(d.line||''));
