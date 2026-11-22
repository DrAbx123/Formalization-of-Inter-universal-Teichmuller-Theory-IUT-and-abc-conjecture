import { readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const queue=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean);
const deps=['tmp/sheaf/xif/paper/Mzk1LiteralIQCarrierActual.lean','tmp/sheaf/xif/paper/GlobalIQHullInterfaceActual.lean','LeanFormal/IUT/IUTII/Frobenioid/Example36LocalGaloisInvariantMonoid.lean'];
for(const f of deps){
  const src=existsSync(ROOT+'/'+f);
  const ole=existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
  console.log(f+' src='+src+' olean='+ole+' queued='+queue.includes(f));
}
