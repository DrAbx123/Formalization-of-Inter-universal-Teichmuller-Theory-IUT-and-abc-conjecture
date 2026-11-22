#!/usr/bin/env node
// Lead gate tool: per-target freshness + forbidden tokens + last watchdog event + last-run axiom prints.
// Usage: node tools/wd_gate.mjs [--write] [PATH...]  (default: dag/watchdog/extra-targets.txt)
import { readFileSync, writeFileSync, existsSync, statSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const WL=ROOT+'/dag/watchdog/extra-targets.txt';
const LOG=ROOT+'/dag/watchdog/watchdog.log';
const OUT=ROOT+'/coord/GATE-LATEST.md';
const norm=p=>p.trim().replaceAll('\\','/').replace(/^D:\/lean\//i,'').replace(/^\.\//,'');
const args=process.argv.slice(2).filter(x=>x!=='--write').map(norm);
const write=process.argv.includes('--write');
const wl=args.length?args:(existsSync(WL)?readFileSync(WL,'utf8').split(/\r?\n/).map(norm).filter(Boolean):[]);
// per-target last event from watchdog.log
const lastEv=new Map();
for(const line of readFileSync(LOG,'utf8').split(/\r?\n/)){
  const m=line.match(/^(\S+) (START|DONE|FAIL|SKIP|SPAWN ERR|TIMEOUT KILL)\b.*?((?:tmp|LeanFormal|Mathlib)[^ ]*\.lean)/);
  if(m) lastEv.set(norm(m[3]),{verb:m[2],ts:m[1]});
}
const oleanOf=(p)=>{ if(p.startsWith('tmp/external/ported/')) return null; return ROOT+'/.lake/build/lib/lean/'+p.replace(/\.lean$/,'')+'.olean'; };
const logOf=(p)=>{ const base=ROOT+'/dag/watchdog/logs/'+p.replace(/[\/\\:]/g,'_')+'.log'; return existsSync(base)?base:null; };
const forbidden=/^\s*(sorry|admit)\b|^\s*axiom\s+|\bPUnit\.|: True\b/;
const rows=[];
for(const p of wl){
  const abs=ROOT+'/'+p;
  let src=null,olean=null,fresh=null,size=0;
  try{ src=statSync(abs); }catch{}
  const op=oleanOf(p); if(op){ try{ olean=statSync(op); }catch{} }
  if(src&&olean) fresh = olean.mtimeMs>=src.mtimeMs;
  let bad=0, badLines=[];
  if(src){ try{ const t=readFileSync(abs,'utf8').split(/\r?\n/); t.forEach((l,i)=>{ if(forbidden.test(l)){ bad++; if(badLines.length<3) badLines.push((i+1)+':'+l.trim().slice(0,100)); } }); }catch{} }
  const ev=lastEv.get(p);
  // last-run axioms: take axiom lines from the LAST contiguous block after the final 'error' or from tail 300 lines
  let axioms='-';
  const lp=logOf(p);
  if(lp){ try{ const lines=readFileSync(lp,'utf8').split(/\r?\n/).filter(Boolean); const tail=lines.slice(-260);
    const ax=tail.filter(l=>/depends on axioms|does not depend on any axioms/.test(l)).map(l=>l.replace(/\s+/g,' ').trim());
    if(ax.length){ const last=ax[ax.length-1]; const mm=last.match(/axioms: \[([^\]]*)\]/); axioms = mm? mm[1].replace(/\s+/g,' '):'no-axioms'; }
  }catch{} }
  rows.push({p,verb:ev?ev.verb:'NO-EVENT',ts:ev?ev.ts:'',fresh:src?(olean?(fresh?'FRESH':'STALE'):'NO-OLEAN'):'NO-SRC',bad,axioms,lines:src?size=src.size:0});
}
const fmt=(r)=>[r.p,r.verb,r.fresh,r.bad===0?'CLEAN':'TOKENS('+r.bad+')',String(r.axioms).slice(0,90)].join('\t');
const head=['path','lastEvent','olean','tokens','axioms(last block)'].join('\t');
const body=rows.map(fmt).join('\n');
const summary={total:rows.length, done:rows.filter(r=>r.verb==='DONE').length, fail:rows.filter(r=>r.verb==='FAIL').length, stale:rows.filter(r=>r.fresh==='STALE').length, noOlean:rows.filter(r=>r.fresh==='NO-OLEAN').length, tokens:rows.filter(r=>r.bad>0).length};
console.log(head); console.log(body); console.log(JSON.stringify(summary));
if(write){ const md=['# GATE-LATEST（wd_gate.mjs 自动生成，'+new Date().toISOString()+'）','','| path | last | olean | tokens | axioms |','|---|---|---|---|---|',...rows.map(r=>'| '+[r.p,r.verb,r.fresh,r.bad===0?'CLEAN':'TOKENS('+r.bad+')',String(r.axioms).slice(0,80)].join(' | ')+' |'),'','summary: '+JSON.stringify(summary)].join('\n'); writeFileSync(OUT,md); console.log('wrote '+OUT); }
