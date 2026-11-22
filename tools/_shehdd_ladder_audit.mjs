import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
const ROOT='D:/lean';
const idx=JSON.parse(readFileSync(ROOT+'/dag/generated/declarations-index.json','utf8')).declarations;
function walk(dir,acc){ for(const e of readdirSync(dir,{withFileTypes:true})){ const p=join(dir,e.name); if(e.isDirectory()){ if(['logs','.lake','.git','vendor','external'].includes(e.name)) continue; walk(p,acc); } else if(e.name.endsWith('.lean')) acc.push(p.replace(/\\/g,'/').replace(ROOT+'/','')); } return acc; }
const files=walk(ROOT+'/LeanFormal',[]).concat(walk(ROOT+'/tmp/sheaf',[]));
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
const declsByFile={}; for(const d of idx){ if(d.file) (declsByFile[d.file]=declsByFile[d.file]||[]).push(d.name); }
const groups={
 'R1': ['SourceLogShellCarrier','PrimeStripsConstruction','SourceHodgeTheater','SourceDThetaConstruction','SourceH1H2Construction','MultiradialAlgorithmReduction','SourceFiniteMultiradial'],
 'R2': ['Ind1Reduction','Ind2Reduction','K1K2BoundaryReduction','SourceColumnCarrierIdentification','SourceProcessionStepXI','SourceAdjacentColumnProcessionIsomorphism'],
 'R3': ['HullDeterminantLogVolumeReduction','PaperIQCarrierActual','S2723GlobalIQHullActual','S3129IQHullLogVolumeSourceActual'],
 'R4': ['ArithmeticQPilot','CardHullRealGeometryGapCards','S1929LiteralIQCarrierActual','SourceSHETransportObligations','Obligations','APT','CertificateHullWiring','ConcreteFiniteRouteColumns','StepXIContract']
};
const L=[];
L.push('# A482: LADDER rung 资产 vs 实际 Lean 声明核对（shehdd 审计）');
L.push('');
L.push('日期: 2026-11-11。来源: coord/LADDER-A482.md 四个 rung 的资产清单（名称 token）+ 本仓库声明索引/文件系统核对。');
L.push('');
L.push('规则: token 解析优先级 = 文件 basename 包含 → 声明名精确/后缀匹配；olean 状态按 .lake/build/lib/lean 对应路径检查。value-model 路线结论按 A481/F2 明确禁止作为 rung。');
L.push('');
for(const [r,tokens] of Object.entries(groups)){
  L.push('## Rung '+r+' 资产核对');
  L.push('');
  L.push('| LADDER token | 实际 file:decl 映射 | olean | 一致性 |');
  L.push('|---|---|---|---|');
  for(const tok of tokens){
    const fh=files.filter(f=>f.split('/').pop().replace(/\.lean$/,'').toLowerCase().includes(tok.toLowerCase())).slice(0,3);
    const dh=idx.filter(d=>(d.name===tok)||d.name.endsWith('.'+tok)).slice(0,3);
    let map='-', ok='MISSING', ole='-';
    if(fh.length){
      const f=fh[0]; const ds=declsByFile[f]||[];
      map=f+':'+(ds.slice(0,4).join(', ')||'(decl index empty)');
      ole=olean(f)?'fresh':'stale';
      ok=fh.length>1?'RENAMED/MULTI ('+fh.length+')':'OK';
      if(fh.length>1){ map=fh.map(x=>x.split('/').pop()).join(' | ')+' :: '+map; }
    } else if(dh.length){
      map=dh.map(d=>d.file+':'+d.name).join(' | ');
      ole='-';
      ok='DECL-ONLY (file named differs)';
    }
    L.push('| '+tok+' | '+map+' | '+ole+' | '+ok+' |');
  }
  L.push('');
}
L.push('## Rung 缺口报告');
L.push('');
L.push('- R1 (BPS -> multiradial representation): 对象资产齐全（SourceLogShellCarrier, PrimeStripsConstruction, SourceHodgeTheater*, SourceDThetaConstruction, SourceH1H2Construction, MultiradialAlgorithmReduction, SourceFiniteMultiradial 均是 tree/paper 已存在模块）。**缺口**: LADDER 要求的“算法打包”（BPS 输入 -> multiradial 输出）尚无单一定理/结构 rung 文件；需以 MultiradialAlgorithmReduction.carrierAlgorithmContract + SourceFiniteMultiradial 为组件新增真实 rung 定理。');
L.push('- R2 (dsc: Ind1/2/3): Ind1Reduction/Ind2Reduction/K1K2BoundaryReduction(Ind3) 均存在；SourceColumnCarrierIdentification/SourceProcessionStepXI/SourceAdjacentColumnProcessionIsomorphism 存在（名称一致）。**缺口**: 四三角合成（Ind1/2/3 联合下降 + 0-column quotient 组装）未有单一 rung 定理。');
L.push('- R3 (hull+det): HullDeterminantLogVolumeReduction(FrozenSpec)、PaperIQCarrierActual、S2723GlobalIQHullActual、S3129IQHullLogVolumeSourceActual 均存在（paper 层资产在 tmp，需 watchdog 编译进 DAG）。**缺口**: literal 载体上的 hull 有限性（Cor 3.12 内容层）尚待 abc/hull 以 product Haar 证明；value-model 的 hull 有限性禁止作为证据（F2）。');
L.push('- R4 (HDD∘SHE): ArithmeticQPilot*（3 文件）、CardHullRealGeometryGapCards、S1929LiteralIQCarrierActual、SourceSHETransportObligations、Obligations.lean(ipl/she -> LeanFormal/IUT/IUTIII/Theorem311/Obligations.lean)、StepXI/APT.lean、CertificateHullWiring、ConcreteFiniteRouteColumns、StepXIContract（声明在 StepXI/Contract.lean:30）均存在。**缺口**: 目标 rung “literal 载体上 3.11.5⇒3.12 的组装” 尚缺；需要把 (hull+det)∘(dsc) 与 SHE/IPL 组装成单一真实定理（当前只有组件）。');
L.push('');
L.push('## 映射修正（LADDER 名称 -> 实际声明名/文件）');
L.push('');
L.push('- StepXIContract 是声明名（LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean:30），不是文件名；');
L.push('- Obligations.lean(ipl/she) 对应 LeanFormal/IUT/IUTIII/Theorem311/Obligations.lean（另有多处 Obligations 文件，注意消歧）；');
L.push('- APT 对应 LeanFormal/IUT/IUTIII/Corollary312/StepXI/APT.lean；');
L.push('- ArithmeticQPilot* 是 3 个文件的族（BaseChange/GlobalNormalization/LogVolume）；');
L.push('- S1929LiteralIQCarrierActual / PaperIQCarrierActual / S2723GlobalIQHullActual / S3129IQHullLogVolumeSourceActual 在 tmp/sheaf/xif/paper（paper 层，需 olean 才入正式 DAG）。');
L.push('');
L.push('## value-model 禁用声明（A481/F2 复核）');
L.push('');
L.push('- 任何以 value-realized/model-carrier hull 有限性（ValueHullCompactnessInput / sourceHullVolume<⊤ 的 value 版本）为基础的结论不得登记为 rung；证据: SourceHullInterfaceDischarge.lean 的 sourceHullVolume_not_lt_top_of_degreeFaithful / not_exists_scaledRegionImage_unitDegreeBounded_of_degreeFaithful / not_nonempty_valueHullCompactnessInput_of_degreeFaithful。');
L.push('');
writeFileSync(ROOT+'/coord/LADDER-A482-AUDIT.md', L.join('\n')+'\n');
console.log('ladder audit written; files resolved='+files.length);
