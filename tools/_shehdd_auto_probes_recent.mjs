import { readFileSync, writeFileSync, existsSync, readdirSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const PAPER=ROOT+'/tmp/sheaf/xif/paper';
const res=readFileSync(ROOT+'/tmp/xif_guarded_results.log','utf8');
const all=readdirSync(PAPER).filter(f=>f.endsWith('.lean'));
const plain=all.filter(f=>!f.startsWith('_')).map(f=>({f,t:statSync(PAPER+'/'+f).mtimeMs})).sort((a,b)=>b.t-a.t);
const targets=[];
for(const {f} of plain){
  const base=f.replace(/\.lean$/,'');
  if(!res.includes('EXIT=0 FILE=tmp/sheaf/xif/paper/'+base+'.lean')) continue;
  const hasProbe=all.some(x=>x.includes(base)&&/Probe|probe/.test(x));
  if(hasProbe) continue;
  const txt=readFileSync(PAPER+'/'+f,'utf8');
  const nsMatch=txt.match(/^namespace\s+([A-Za-z0-9_.']+)\s*$/m);
  if(!nsMatch) continue;
  const ns=nsMatch[1];
  const decls=[...txt.matchAll(/^(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_'.]+)/gm)].map(m=>m[1]).filter(d=>d!=='sorryAx').slice(0,3);
  if(decls.length===0) continue;
  targets.push({base,ns,decls});
  if(targets.length>=15) break;
}
let n=0;
for(const t of targets){
  writeFileSync(PAPER+'/_AutoProbe_'+t.base+'.lean','import tmp.sheaf.xif.paper.'+t.base+'\n\n'+t.decls.map(d=>'#print axioms '+t.ns+'.'+d).join('\n')+'\n');
  n++;
}
const extra=ROOT+'/dag/watchdog/extra-targets.txt';
let existing=''; try{ existing=readFileSync(extra,'utf8'); }catch{}
const add=targets.map(t=>'tmp/sheaf/xif/paper/_AutoProbe_'+t.base+'.lean').filter(x=>!existing.includes(x));
if(add.length) writeFileSync(extra, existing+(existing.endsWith('\n')?'':'\n')+add.join('\n')+'\n');
console.log('recent probes written='+n);
console.log(targets.map(t=>t.base).join(','));
