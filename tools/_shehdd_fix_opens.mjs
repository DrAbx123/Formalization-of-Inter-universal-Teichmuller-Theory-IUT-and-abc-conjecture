import { readFileSync, writeFileSync } from 'node:fs';
const ROOT='D:/lean';
const fixes=[
 ['tmp/sheaf/xif/paper/ShehddQParameterConsumerActual.lean','open LeanFormal.IUT.ArithmeticQPilotLogVolume','open LeanFormal.IUT.ArithmeticQPilotLogVolume\nopen LeanFormal.IUT.NumberFieldFinitePlace'],
 ['tmp/sheaf/xif/paper/ShehddLocalLogInverseConsumerActual.lean','open LeanFormal.IUT.LocalFieldLogarithm','open LeanFormal.IUT.LocalFieldLogarithm\nopen LeanFormal.IUT.LocalFieldIntegralUnits'],
 ['tmp/sheaf/xif/paper/ShehddIntegralUnitLogConsumerActual.lean','open LeanFormal.IUT.LocalFieldLogarithm','open LeanFormal.IUT.LocalFieldLogarithm\nopen LeanFormal.IUT.LocalFieldIntegralUnits']
];
for(const [rel,oldS,newS] of fixes){
  const p=ROOT+'/'+rel;
  const txt=readFileSync(p,'utf8');
  if(txt.includes(newS)){ console.log(rel+' already fixed'); continue; }
  if(!txt.includes(oldS)){ console.log(rel+' pattern not found'); continue; }
  writeFileSync(p, txt.replace(oldS,newS));
  console.log(rel+' open added');
}
