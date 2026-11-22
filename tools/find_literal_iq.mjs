import { readdirSync, readFileSync } from 'node:fs';
const ROOT='D:/lean';
function walk(d,out){ let e=[]; try{e=readdirSync(d,{withFileTypes:true})}catch{ return out; } for(const x of e){ const p=d+'/'+x.name; if(x.isDirectory()) walk(p,out); else if(x.name.endsWith('.lean')) out.push(p); } return out; }
const files=walk(ROOT+'/LeanFormal',[]).concat(walk(ROOT+'/tmp/sheaf/xif/paper',[]));
const out=[];
for(const f of files){ let s=''; try{ s=readFileSync(f,'utf8'); }catch{ continue; } if(/LiteralArithmeticHullInterface|LiteralIQ|IQCarrierLiteral|literalIQ|IQ\(S/.test(s)) out.push(f.replace(ROOT+'/','')); }
console.log('hits',out.length); console.log(out.slice(0,40).join('\n'));