import { readFileSync } from 'node:fs';
const strip=(s)=>{ let out=''; let i=0; const n=s.length; while(i<n){ if(s.startsWith('/-',i)){ let depth=1; i+=2; while(i<n && depth>0){ if(s.startsWith('/-',i)){ depth++; i+=2; } else if(s.startsWith('-/',i)){ depth--; i+=2; } else i++; } continue; } if(s.startsWith('--',i)){ const j=s.indexOf('\n',i); i=(j<0?n:j); continue; } if(s[i]==='"'){ i++; while(i<n){ if(s[i]==='\\'){ i+=2; continue; } if(s[i]==='"'){ i++; break; } i++; } out+=' '; continue; } out+=s[i]; i++; } return out; };
const f='Iut/Foundations/SourceFrobenioidSystemReindexConstant.lean';
const code=strip(readFileSync('D:/lean/'+f,'utf8'));
const re=/^\s*(axiom|constant|opaque)\s+([A-Za-z0-9_'.]+)/gm; let m;
while((m=re.exec(code))){ const line=code.slice(0,m.index).split('\n').length; console.log('line',line,'::',JSON.stringify(code.split('\n')[line-1])); }