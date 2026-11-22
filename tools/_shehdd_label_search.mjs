import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8'));
const decls=idx.declarations||[];
const pats=[
 /identif/i,
 /cor4[._]?10|corollary4[._]?10/i,
 /f_l|flstar|fl_?star/i,
 /invariantimage/i,
 /labelfinite|finiteLabel/i
];
for(const re of pats){
  const hits=decls.filter(d=>re.test(d.name));
  console.log('/'+re.source+'/ hits='+hits.length);
  for(const h of hits.slice(0,10)) console.log('   '+h.name+' | '+h.file+':'+(h.line||''));
}
