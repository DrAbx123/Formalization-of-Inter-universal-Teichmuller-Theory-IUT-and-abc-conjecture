import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/tmp/external/Takkun-IUT_LEAN/IutLean';
const files=['Frobenioid/PrimeStrip.lean','Frobenioid/PrimeStripSystem.lean','HodgeTheater/PrimeStripData.lean','HodgeTheater/Defs.lean','LogTheta/LogShell.lean','LogTheta/Lattice.lean','LogTheta/LatticeConcrete.lean','LogTheta/Indeterminacy.lean','InitialThetaData/Defs.lean','Theta/ThetaValues.lean','Arithmetic/RealHodgeTheater.lean','Arithmetic/RealFrobenioid.lean','Arithmetic/RealKummer.lean'];
for(const rel of files){
  const t=readFileSync(p+'/'+rel,'utf8').split('\n');
  console.log('===== '+rel+' lines='+t.length);
  for(let i=0;i<t.length;i++){
    if(/^(structure|inductive|class) /.test(t[i])){
      let acc=t[i].trim(); let j=i+1; let depth=0;
      while(j<t.length && j<i+60){ const s=t[j].trim(); if(s.startsWith('where')){ acc+=' '+s; j++; break; } acc+=' '+s; if(/where\s*$/.test(s)){ j++; break;} j++; }
      console.log('  L'+(i+1)+': '+acc.slice(0,600));
    }
  }
}
