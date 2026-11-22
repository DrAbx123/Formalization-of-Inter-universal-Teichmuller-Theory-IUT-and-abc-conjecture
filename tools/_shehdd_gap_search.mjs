import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8'));
const decls=idx.declarations||[];
console.log('index decls='+decls.length);
const groups={
 qParam:/qparam|q_param|qparameter|q-parameter|qnorm|q_norm/i,
 thetaPilot:/thetapilot|theta_pilot|theta-pilot|sourcethetapilot/i,
 labels:/cor410|cor4_10|thetalabel|theta_label|labelident|labelidentif|labelzero|zerolabel|f_l|flabel/i,
 h6precise:/geometriccoreprecise|geomcoreprecise|precisegeometriccore|h6precise|h6_precise/i,
 sources1995:/1995|faltings|sources1995|sourcetheorems/i,
 fixedBeta:/fixedbeta|fixed_beta/i,
 schemeSide:/schemeside|sectionmap|placepoint|fibrebridge/i,
 problemD:/problemdapplic|problem_d_applic/i
};
for(const [k,re] of Object.entries(groups)){
  const hits=decls.filter(d=>re.test(d.name)||re.test(d.file||''));
  console.log(k+' hits='+hits.length);
  for(const h of hits.slice(0,8)) console.log('   '+h.name+' | '+h.file+':'+(h.line||''));
}
