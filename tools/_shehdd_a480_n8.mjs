import { readFileSync, writeFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const d=JSON.parse(readFileSync(ROOT+'/dag/declaration-dag.json','utf8'));
const audit=['C3CompleteSourceReduction','C5Native','C9PaperClosure','N8RouteClosure','C1InfiniteUnitQuotientAttempt','C1QuotientConsumerProbe','C3GaloisUnitFixedAttempt','C3SourceGaloisActionAttempt','C3TensorConstruction','C9P6Closure','FiniteObservationHull','IPLFamilyData','NativeC3','P6Bridge','P6ChainA','P6ChainB','P6Comparison','P6EllOutBridgeAttempt','P6IndInvarianceAttempt','P6L','P6RelaxedGlobalReadout','P6SHEInd','P6SourceVolumeCarrierMapAttempt','PaperNormalizedVolume','PaperValuesBoundedReduction','SourceAlgorithmCompatibility','SourceAllowedOutputActualAttempt','SourcePilotApproximation','SourcePilotApproximationIQ','TargetSignature','UnitSphereReadoutDonorActual'];
const auditSet=new Set(audit.map(a=>'tmp/sheaf/n8/closure/'+a));
const inDeg=new Map(), extMap=new Map();
for(const e of d.edges){
  const to=(e.to||'').replace(/^olean:/,'').replace(/\.lean$/,'');
  if(auditSet.has(to)){
    if(!inDeg.has(to)) inDeg.set(to,[]); inDeg.get(to).push(e.from);
    if(!(e.from||'').includes('tmp/sheaf/n8/')){ if(!extMap.has(to)) extMap.set(to,[]); extMap.get(to).push(e.from); }
  }
}
const triage=audit.map(a=>{
  const mod='tmp/sheaf/n8/closure/'+a;
  const users=(inDeg.get(mod)||[]).length;
  const ext=(extMap.get(mod)||[]);
  return {a,mod,users,ext,olean:existsSync(ROOT+'/.lake/build/lib/lean/'+mod+'.olean')};
});
const tier=(r)=>{
  if(r.ext.length>0) return 1;
  if(r.users>=5) return 2;
  if(r.users>=1) return 3;
  return 4;
};
triage.forEach(r=>r.tier=tier(r));
triage.sort((x,y)=>x.tier-y.tier||y.users-x.users);
const L=[];
L.push('# A480-A: tmp/sheaf/n8 legacy 31 个 sorry 模块修复优先级（只读 triage）');
L.push('');
L.push('来源: dag/SORRY-AUDIT.md（n8 31 模块, 全部 olean 已编译且含 sorry）+ dag/declaration-dag.json import 边（olean 真源）统计。判定: 是否被 n8 外部模块 import = 是否进入 IUT 主链的可达路径。');
L.push('');
L.push('## 结论（一行）');
L.push('');
const t1=triage.filter(r=>r.tier===1).length,t2=triage.filter(r=>r.tier===2).length,t3=triage.filter(r=>r.tier===3).length,t4=triage.filter(r=>r.tier===4).length;
L.push('- 31 个中 **'+t1+' 个被 n8 外部模块引用**（Tier1，主链可达，优先修）；'+t2+' 个仅被 n8 内部高频引用（Tier2，n8 route 修复才有意义）；'+t3+' 个仅少量内部引用（Tier3）；'+t4+' 个零引用（Tier4，死端，建议 DAG-BLOCKED/归档）。');
L.push('- 无任何 LeanFormal/IUT 主链模块直接 import n8 sorry 模块；Tier1 的外部引用均来自 tmp/sheaf/xif/paper 的 paper 层链（C3/native、P6、S2xxx 等）。故修复价值取决于 paper 层消费者链是否进入 Cor 3.12 / ABC 主链。');
L.push('');
L.push('## Tier 1（有外部消费者；优先修）');
L.push('');
L.push('| 模块 | sorry | 外部消费者（数量） | 修复理由 |');
L.push('|---|---|---|---|');
for(const r of triage.filter(r=>r.tier===1)){
  const extNames=r.ext.map(x=>x.replace(/^olean:/,'')).slice(0,4).join(', ');
  L.push('| '+r.a+' | ? | '+r.ext.length+'（'+extNames+'） | 被 paper 层引用，修好后可把 paper 层 consumer 链闭合（C3/native 或 P6 路线） |');
}
L.push('');
L.push('注: 31 个模块的 sorry 数见 dag/SORRY-AUDIT.md（C3CompleteSourceReduction 3、C5Native 2、C9PaperClosure 2、N8RouteClosure 2，其余各 1）。');
L.push('');
L.push('## Tier 2（n8 内部高频 hub；仅当 n8 route 重启时修）');
L.push('');
L.push('| 模块 | n8 内部使用者数 |');
L.push('|---|---|');
for(const r of triage.filter(r=>r.tier===2)) L.push('| '+r.a+' | '+r.users+' |');
L.push('');
L.push('## Tier 3（少量内部引用；保持 CONDITIONAL/登记）');
L.push('');
L.push('| 模块 | n8 内部使用者数 |');
L.push('|---|---|');
for(const r of triage.filter(r=>r.tier===3)) L.push('| '+r.a+' | '+r.users+' |');
L.push('');
L.push('## Tier 4（零引用；建议 DAG-BLOCKED 归档）');
L.push('');
L.push('| 模块 |');
L.push('|---|');
for(const r of triage.filter(r=>r.tier===4)) L.push('| '+r.a+' |');
L.push('');
L.push('## 建议动作');
L.push('');
L.push('1. P1（Tier1）：先修 NativeC3（外部 18 个消费者，C3/native q-pilot donor 链）、C3TensorConstruction（FmodTensorLanding/TensorUnconditional 消费）、P6ChainA（S2556/S2557 paper 路线）、SourceAllowedOutputActualAttempt（S2561）；每个用真实证明/已编译 tree 资产替代 sorry，不能则登记 DAG-BLOCKED。');
L.push('2. P2（Tier2）：C9PaperClosure/P6L/P6Comparison/P6Bridge/SourceAlgorithmCompatibility/IPLFamilyData 等 n8 内部 hub 暂不修，等 Tier1 链路恢复后再评估。');
L.push('3. P3（Tier4）：C1QuotientConsumerProbe/C3GaloisUnitFixedAttempt/SourcePilotApproximation 等零引用模块登记 DAG-BLOCKED（原因: n8 legacy route 无消费者、非 IUT 主链可达）并保留历史。');
L.push('4. 不删除任何历史文件/条目。');
writeFileSync(ROOT+'/coord/N8-SORRY-TRIAGE-A480.md', L.join('\n')+'\n');
console.log('N8 triage written; tiers: T1='+t1+' T2='+t2+' T3='+t3+' T4='+t4);
for(const r of triage.filter(r=>r.tier===1)) console.log('T1 '+r.a+' ext='+r.ext.length+' users='+r.users);
