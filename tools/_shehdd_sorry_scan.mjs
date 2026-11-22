import { readFileSync } from 'node:fs';
const ROOT='D:/lean';
const files=['tmp/sheaf/xif/paper/S1794FiberFunctorProductActual.lean','tmp/sheaf/n8/closure/C3CompleteSourceReduction.lean','tmp/sheaf/n8/closure/C5Native.lean','tmp/sheaf/n8/closure/C9PaperClosure.lean','tmp/sheaf/n8/closure/N8RouteClosure.lean','tmp/sheaf/xif/paper/IUTExternal32GateV36Actual.lean','tmp/sheaf/xif/paper/S2432PrestackCloseActual.lean','tmp/sheaf/xif/paper/S2748AbsNormGeRationalPrimeActual.lean','tmp/sheaf/xif/paper/_S2519HIdProbe.lean'];
for(const rel of files){
  const txt=readFileSync(ROOT+'/'+rel,'utf8').split('\n');
  const idxs=[]; txt.forEach((l,i)=>{ if(/\bsorry\b/.test(l)) idxs.push(i); });
  if(!idxs.length) continue;
  console.log('=== '+rel+' sorry@'+(idxs.map(i=>i+1).join(',')));
  for(const i of idxs){
    // find enclosing theorem/def start upward
    let j=i; while(j>0 && !/^(theorem|def|noncomputable def|lemma|instance)\b/.test(txt[j].trim())) j--;
    const stmt=txt.slice(j, Math.min(i+1, j+8)).map(s=>s.trim()).join(' ');
    console.log('  @'+(i+1)+' enclosing: '+stmt.slice(0,300));
  }
}
