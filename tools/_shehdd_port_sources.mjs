import { readFileSync, writeFileSync, existsSync, mkdirSync, copyFileSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const FOUND='LeanFormal/IUT/Foundations/AlgebraicGeometry';
const STAGE=['tmp/n8-20261018/general','tmp/n8-20261018/compile-root/LeanFormal/IUT','tmp/n8-20261018/puncturebuild'];
const legacy=['AdicCompletionFractionField','SourcePsiResidueRingFinite','SourcePsiIntegralModelMinimality','SourcePsiMinimalModelCriterion','SourcePsiMinimalModelConverse','SourcePsiUniformizerAbsorptionFinal','SourcePsiReductionSpecialFiber','SourcePsiReductionModelComparison','SourcePsiGradedRingActual'];
const staging=(name)=>{ for(const d of STAGE){ const p=ROOT+'/'+d+'/'+name+'.lean'; if(existsSync(p)) return p; } return null; };
const repoPath=(mod)=>{ const p=ROOT+'/'+mod.replaceAll('.','/')+'.lean'; return existsSync(p)?p:null; };
const legacySet=new Set(legacy);
const rewrite=(txt)=>{
  return txt.split('\n').map(line=>{
    const m=line.match(/^import\s+(\S+)\s*$/);
    if(!m) return line;
    const imp=m[1];
    const last=imp.split('.').pop();
    if(legacySet.has(last)) return 'import '+FOUND.replaceAll('/','.')+'.'+last;
    if(!repoPath(imp)){ const st=staging(last); if(st){ legacySet.add(last); legacy.push(last); return 'import '+FOUND.replaceAll('/','.')+'.'+last; } }
    return line;
  }).join('\n');
};
// port recursively (loop until stable)
let changed=true; const portedList=[];
while(changed){
  changed=false;
  for(let i=0;i<legacy.length;i++){
    const name=legacy[i];
    const dst=ROOT+'/'+FOUND+'/'+name+'.lean';
    if(existsSync(dst)) continue;
    const src=staging(name); if(!src) continue;
    const txt=rewrite(readFileSync(src,'utf8'));
    mkdirSync(join(ROOT,FOUND),{recursive:true});
    writeFileSync(dst,txt,'utf8');
    portedList.push(name); changed=true;
  }
}
console.log('ported: '+portedList.join(', '));
