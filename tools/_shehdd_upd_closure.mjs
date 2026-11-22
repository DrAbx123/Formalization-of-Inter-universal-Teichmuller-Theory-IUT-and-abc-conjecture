import { readFileSync, appendFileSync } from 'node:fs';
const ROOT='D:/lean';
const p=ROOT+'/coord/F4B-STEPPROVIDER-CLOSURE.md';
let t=readFileSync(p,'utf8');
if(!t.includes('CVCompositionLawF 已证')){
  const esc=String.fromCharCode(39);
  const add=['','## CVCompositionLawF 已证（A480 本轮新结果）','',
  '- tmp/sheaf/xif/paper/ShehddCVCompositionLawProvedActual.lean:',
  '  - cvCompositionLawF_proved: 用形式导数链式法则 Polynomial.derivative_comp + mul_eq_zero + Polynomial.aeval_comp，对 Qbar 上任意多项式证明临界值复合法则（原 named input）；',
  '  - stepTransport_of_goal_unconditional: stepTransport_of_goal 现在不再需要 CVCompositionLawF 假设。',
  '- 因此 fixedBeta 收口后剩余 named 输入只剩: 归一化 f0 存在且 f0(beta) 不在 S'+esc+'（解析回避层）。',
  '- stepProvider 收敛仍需该几何回避层；CV 侧已闭合。',''];
  appendFileSync(p, add.join('\n'));
  console.log('closure doc updated');
} else console.log('already updated');
