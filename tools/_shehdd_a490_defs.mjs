import { readFileSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const dir=ROOT+'/tmp/sheaf/lana/iut/Iut';
function walk(x,acc){ for(const e of readdirSync(x,{withFileTypes:true})){ const p=x+'/'+e.name; if(e.isDirectory()) walk(p,acc); else if(e.name.endsWith('.lean')) acc.push(p); } return acc; }
const files=walk(dir,[]).concat(walk(ROOT+'/tmp/sheaf/lana/iut/Iut4Sec1',[]));
const pats=[/^(def|abbrev|structure) Region /,/^(def|abbrev) IsAdelic/,/^(def|abbrev) InHullOfImage/,/^(def|abbrev) etaQ/,/^(def|abbrev) qVal/,/^structure Rss/,/^namespace Rss/,/^(def|abbrev) rssEquiv/,/theorem exists_adelic_iff/,/^structure Region/];
for(const p of pats){
  console.log('PATTERN '+p);
  let shown=0;
  for(const f of files){ const t=readFileSync(f,'utf8').split('\n'); for(let i=0;i<t.length;i++){ if(p.test(t[i])){ console.log('  '+f.replace(ROOT+'/tmp/sheaf/lana/','')+':'+(i+1)+': '+t[i].trim().slice(0,140)); shown++; if(shown>5) break; } } if(shown>5) break; }
}
