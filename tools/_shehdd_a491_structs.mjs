import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const iut=ROOT+'/tmp/sheaf/lana/iut/Iut';
const files=['Wall/BPS.lean','Wall/EtaAlg.lean','Wall/Checks.lean','Wall/Constraints.lean','Wall/Rss.lean','Wall/QPilotRegion.lean','Wall/MultiContainer.lean','Wall/IdentifiedCopies.lean','Cor312/Statement.lean','Cor312/LeftHandSide.lean','Cor312/RightHandSide.lean','Cor312/Container.lean','Cor312/ContainerHull.lean','Cor312/HolomorphicHull.lean','Cor312/LogVolume.lean','Cor312/PacketPresentation.lean','Cor312/Procession.lean','Cor312/RationalPlace.lean'];
for(const rel of files){
  const f=iut+'/'+rel; if(!existsSync(f)){ console.log('MISS '+rel); continue; }
  const t=readFileSync(f,'utf8').split('\n');
  console.log('===== '+rel);
  for(let i=0;i<t.length;i++){
    if(/^(structure|inductive|class) /.test(t[i])){
      let j=i, body=[];
      while(j<t.length && j<i+40){ body.push(t[j].trim()); if(t[j].includes('deriving')||(t[j].trim()==='' && body.length>2)) break; j++; }
      console.log('  L'+(i+1)+': '+body.slice(0,22).join(' ').slice(0,700));
    }
  }
}
console.log('--- Concrete files ---');
const cdir=iut+'/Concrete';
if(existsSync(cdir)) console.log(readdirSync(cdir).filter(x=>x.endsWith('.lean')).join(', '));
