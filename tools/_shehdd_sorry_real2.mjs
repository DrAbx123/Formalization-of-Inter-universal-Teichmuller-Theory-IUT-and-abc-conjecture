import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const audit=readFileSync(ROOT+'/dag/SORRY-AUDIT.md','utf8');
const files=[...audit.matchAll(/^\| (\S+\.lean) \| (\d+) \|/gm)].map(m=>({file:m[1],count:+m[2]}));
function codeText(s){
  let out=''; let i=0; const n=s.length;
  while(i<n){
    const c=s[i], c2=s.slice(i,i+2);
    if(c2==='/-'){ let depth=1; i+=2; while(i<n&&depth>0){ const d=s.slice(i,i+2); if(d==='/-'){depth++;i+=2;} else if(d==='-/'){depth--;i+=2;} else i++; } continue; }
    if(c2==='--'){ while(i<n&&s[i]!=='\n') i++; continue; }
    if(c==='"'){ i++; while(i<n&&s[i]!=='"'){ if(s[i]==='\\') i+=2; else i++; } i++; continue; }
    if(c==="'"){ // char literal or quoted ident; approximate
      if(i+2<n && (s[i+2]==="'" || (s[i+1]==='\\' && i+3<n && s[i+3]==="'"))){ i++; while(i<n&&s[i]!=="'"){ if(s[i]==='\\') i+=2; else i++; } i++; continue; }
      out+=c; i++; continue;
    }
    out+=c; i++;
  }
  return out;
}
let realTotal=0; const rows=[];
for(const f of files){
  const txt=readFileSync(ROOT+'/'+f.file,'utf8');
  const real=(codeText(txt).match(/\bsorry\b/g)||[]).length;
  realTotal+=real; rows.push({file:f.file,audit:f.count,real});
}
console.log('audit_total='+files.reduce((a,b)=>a+b.count,0)+' real_total='+realTotal);
for(const r of rows) if(r.audit!==r.real) console.log('  '+r.file+' audit='+r.audit+' real='+r.real);
const L=[];
L.push('# A480: SORRY-AUDIT 交叉核对（shehdd；按 Lean 词法去注释/字符串）');
L.push('');
L.push('方法: 对 dag/SORRY-AUDIT.md 的 36 模块做字符级 Lean 词法扫描（嵌套块注释/行注释/字符串/字符字面量），只统计源码中的 sorry token。');
L.push('');
L.push('- 审计文件: '+files.length+' 模块 / '+files.reduce((a,b)=>a+b.count,0)+' 处。');
L.push('- **真实源码 sorry total = '+realTotal+'**。');
L.push('');
L.push('| file | audit | 真实 sorry | 说明 |');
L.push('|---|---|---|---|');
for(const r of rows) if(r.audit!==r.real){
  let why='';
  if(r.real<r.audit) why = r.real===0 ? '纯文案字符串/已修复，无需处理' : '部分为文案或已修复';
  else why='审计低估';
  L.push('| '+r.file+' | '+r.audit+' | '+r.real+' | '+why+' |');
}
L.push('');
L.push('## 结论');
L.push('');
L.push('- 假阳性（真实 0）: 见上表；不计入修复任务。');
L.push('- 真实 sorry 仍集中在 n8 closure 与 paper 模块；对应 OBSTRUCTION 已在 coord/DAG-BLOCKED.json 登记，修复优先级见 coord/N8-SORRY-TRIAGE-A480.md。');
L.push('- 建议: SORRY-AUDIT 生成器改用同样词法过滤，避免 ledger 文案混入统计。');
L.push('');
writeFileSync(ROOT+'/coord/SORRY-AUDIT-CORRECTION-shehdd.md', L.join('\n')+'\n');
console.log('correction doc rewritten');
