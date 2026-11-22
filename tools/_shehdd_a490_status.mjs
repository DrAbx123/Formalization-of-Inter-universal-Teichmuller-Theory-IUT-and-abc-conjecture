import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const files=['tmp/sheaf/lana/iut/Iut/Wall/NumericalWallHullActual.lean','tmp/sheaf/lana/iut/Iut/Wall/NumericalWallRssActual.lean','tmp/sheaf/lana/iut/Iut/Wall/Checks.lean','tmp/sheaf/lana/iut/Iut/Wall/IdentifiedCopies.lean','tmp/sheaf/lana/iut/Iut/Wall/QPilotRegion.lean','tmp/sheaf/lana/iut/Iut/Wall/Rss.lean','tmp/sheaf/lana/iut/Iut/Wall/EtaAlg.lean','tmp/sheaf/lana/iut/Iut/Wall/Ind3.lean','tmp/sheaf/lana/iut/Iut/Wall/MultiContainer.lean','tmp/sheaf/lana/iut/Iut/Wall/Scaling.lean','tmp/sheaf/lana/iut/Iut/Wall/Pilots.lean','tmp/sheaf/lana/iut/Iut/Wall/BPS.lean','tmp/sheaf/lana/iut/Iut/Wall/Constraints.lean','tmp/sheaf/lana/iut/Iut/Wall/MultiConstraints.lean'];
for(const f of files){
  const ole=existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
  const log='dag/watchdog/logs/'+f.replace(/\//g,'_')+'.log';
  let errs=[]; let lt='-';
  if(existsSync(ROOT+'/'+log)){ lt='log'; errs=readFileSync(ROOT+'/'+log,'utf8').split('\n').filter(l=>l.includes(': error')).slice(0,2); }
  console.log(f.split('/').pop()+' olean='+ole+(errs.length?' ERR: '+errs[0].trim().slice(0,150):''));
}
// search for existing bridge theorem names
const dir=ROOT+'/tmp/sheaf/lana/iut/Iut';
function walk(x,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const p=x+'/'+e.name; if(e.isDirectory()) walk(p,acc); else if(e.name.endsWith('.lean')) acc.push(p); } return acc; }
const all=walk(dir,[]);
for(const pat of [/numericalWall_iff_le_rhs/,/numericalWall_of_le_rhs/,/le_rhs_of_numericalWall/,/numericalWall.*iff.*rhs/]){
  const hits=[];
  for(const f of all){ const t=readFileSync(f,'utf8'); if(pat.test(t)) hits.push(f.replace(ROOT+'/','')); }
  console.log('PAT '+pat+' hits='+hits.length+(hits.length?' : '+hits.join(', '):''));
}
