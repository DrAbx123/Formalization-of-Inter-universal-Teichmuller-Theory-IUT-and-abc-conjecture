import { readFileSync, existsSync, statSync } from 'node:fs';
const ROOT='D:/lean';
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean);
const queue=new Set(readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean));
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
const resolve=(imp)=>{
  if(imp.startsWith('tmp.sheaf.')) return 'tmp/sheaf/'+imp.slice('tmp.sheaf.'.length).replace(/\./g,'/')+'.lean';
  if(imp.startsWith('LeanFormal.')) return imp.replace(/\./g,'/')+'.lean';
  if(imp.startsWith('Iut.')) return imp.replace(/\./g,'/')+'.lean';
  return null;
};
const need=[];
for(const f of prio){
  if(!existsSync(ROOT+'/'+f)||olean(f)) continue;
  const txt=readFileSync(ROOT+'/'+f,'utf8');
  const imports=txt.split('\n').filter(l=>l.startsWith('import ')).map(l=>l.slice(7).trim());
  for(const imp of imports){ const p=resolve(imp); if(!p) continue; if(!existsSync(ROOT+'/'+p)) continue; if(!olean(p)&&!queue.has(p)) need.push({from:f.split('/').pop(),dep:p}); }
}
const seen=new Set(); const uniq=[];
for(const n of need){ if(!seen.has(n.dep)){ seen.add(n.dep); uniq.push(n); } }
console.log('missing unqueued non-olean deps of critical-path files: '+uniq.length);
for(const n of uniq) console.log('  '+n.dep+'   (needed by '+n.from+')');
