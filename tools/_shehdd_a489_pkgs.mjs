import { readFileSync, existsSync, readdirSync } from 'node:fs';
const ROOT='D:/lean';
const base=ROOT+'/tmp/dsh-oct6-openai-math-survey-20261016/repos/lana';
function decls(path,max){ if(!existsSync(path)) return ['MISSING '+path]; const t=readFileSync(path,'utf8').split('\n'); const out=[]; for(let i=0;i<t.length&&out.length<max;i++){ if(/^(theorem|def|structure|abbrev) /.test(t[i])) out.push(t[i].trim().split(/\s/)[1]); } return out; }
const specs=[
 ['genl','genl/genl-master/Genl/Curves/Theory.lean'],
 ['genl','genl/genl-master/Genl/GeneralPosition.lean'],
 ['heights','heights/heights-master/Heights/Basic.lean'],
 ['tate-curves-theta','tate-curves-theta/tate-curves-theta-main/TateCurvesTheta/Basic.lean'],
 ['padic-log-volume','padic-log-volume/padic-log-volume-main/PadicLogVolume/Basic.lean'],
 ['elliptic-curves','elliptic-curves/elliptic-curves-main/EllipticCurves/Basic.lean']
];
for(const [pkg,rel] of specs){ const p=base+'/'+rel; console.log(pkg+' :: '+rel+' -> '+decls(p,8).join(', ')); }
console.log('--- package dir candidates ---');
for(const pkg of ['genl','heights','tate-curves-theta','padic-log-volume','elliptic-curves']){ const d=base+'/'+pkg; if(existsSync(d)){ console.log(pkg+': '+readdirSync(d).join(', ')); } }
