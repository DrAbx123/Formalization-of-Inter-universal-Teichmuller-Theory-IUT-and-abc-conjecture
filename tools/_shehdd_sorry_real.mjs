import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const audit=readFileSync(ROOT+'/dag/SORRY-AUDIT.md','utf8');
const files=[...audit.matchAll(/^\| (\S+\.lean) \| (\d+) \|/gm)].map(m=>({file:m[1],count:+m[2]}));
function strip(txt){
  let s=txt;
  for(let k=0;k<12;k++){ const before=s.length; s=s.replace(/\/-[\s\S]*?-\//g,' '); if(s.length===before) break; }
  s=s.split('\n').map(l=>l.replace(/--.*$/,'')).join('\n');
  s=s.replace(/"(?:[^"\\]|\\.)*"/g,'""');
  s=s.replace(/'(?:[^'\\]|\\.)'/g,"''");
  return s;
}
let realTotal=0; const rows=[];
for(const f of files){
  const txt=readFileSync(ROOT+'/'+f.file,'utf8');
  const real=(strip(txt).match(/\bsorry\b/g)||[]).length;
  realTotal+=real; rows.push({file:f.file,audit:f.count,real});
}
console.log('audit files='+files.length+' audit_total='+files.reduce((a,b)=>a+b.count,0)+' real_total='+realTotal);
for(const r of rows) if(r.audit!==r.real) console.log('  '+r.file+' audit='+r.audit+' real='+r.real);
const L=[];
L.push('# A480: SORRY-AUDIT 交叉核对（shehdd）');
L.push('');
L.push('方法: 对 dag/SORRY-AUDIT.md 的 36 模块，去嵌套块注释/行注释/字符串字面量后重新统计 sorry token（Lean 真实 sorry；纯文案字符串不计）。');
L.push('');
L.push('- 审计文件: '+files.length+' 模块 / '+files.reduce((a,b)=>a+b.count,0)+' 处（naive 统计）。');
L.push('- 真实 sorry total = '+realTotal+'。');
L.push('');
L.push('| file | audit | 真实 sorry |');
L.push('|---|---|---|');
for(const r of rows) if(r.audit!==r.real) L.push('| '+r.file+' | '+r.audit+' | '+r.real+' |');
L.push('');
L.push('## 假阳性（纯文案字符串，真实 sorry=0）');
L.push('');
for(const r of rows) if(r.real===0) L.push('- '+r.file+'（audit='+r.audit+'，真实=0）');
L.push('');
L.push('## 结论');
L.push('');
L.push('- 假阳性文件无需修；真实 sorry 集中在 n8 closure 与 5 个 paper 模块（见 A480 triage 与 blocked 登记）。');
L.push('- 建议: SORRY-AUDIT 生成器忽略注释/字符串后再统计，避免 ledger 文案计入 sorry。');
L.push('');
writeFileSync(ROOT+'/coord/SORRY-AUDIT-CORRECTION-shehdd.md', L.join('\n')+'\n');
console.log('correction doc written');
