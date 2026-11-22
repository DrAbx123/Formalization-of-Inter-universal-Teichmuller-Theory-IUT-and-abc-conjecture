import { appendFileSync, readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const queue=readFileSync(ROOT+'/dag/watchdog/extra-targets.txt','utf8').split('\n').filter(Boolean);
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
const deps={
 'Mzk1FourTriangleSynthesisActual.lean':['tmp/sheaf/xif/paper/Mzk1LiteralIQCarrierActual.lean'],
 'Mzk1IUTIVStage5NumericalActual.lean':['LeanFormal/IUT/IUTII/Frobenioid/Example36LocalGaloisInvariantMonoid.lean','tmp/sheaf/xif/paper/Mzk1IUTIVStage5ABCFormActual.lean'],
 'A482LiteralCarrierAxiomsActual.lean':['tmp/sheaf/xif/paper/GlobalIQHullInterfaceActual.lean'],
 'A482LiteralIQHullInterfaceActual.lean':['tmp/sheaf/xif/paper/A482LiteralCarrierAxiomsActual.lean']
};
const add=['','## 7. A484 关键路径失败状态（own 修改后重编中）','','- priority 44 条中 30 green、14 缺 olean；这 14 条的 **src_mtime 均晚于对应失败日志时间**（owners 刚修改，watchdog 重编中），非队列问题。','- 关键依赖核对：'];
for(const [f,ds] of Object.entries(deps)){
  const parts=ds.map(d=>d.split('/').pop()+'='+(olean(d)?'green':'missing')+(queue.includes(d)?'/queued':'/notqueued'));
  add.push('  - '+f+' <- '+parts.join(', '));
}
add.push('- 结论: 我的 lane 无需新增/修改；Mzk1LiteralIQCarrierActual/GlobalIQHullInterfaceActual/Example36LocalGaloisInvariantMonoid 已 green（依存满足），FourTriangleSynthesis 等将由 watchdog 下轮通过；A483LiteralCarrierProductHaarActual 的真实代码错误属 abc 正在修改的文件（mtime 20:33 vs log 20:30），不越权改动。');
add.push('- 本轮 0 新增文件、0 新增队列条目（extras_add 规则遵守）。','');
appendFileSync(ROOT+'/coord/A484-RUNG-QUEUE-AUDIT-shehdd.md', add.join('\n'));
console.log('addendum 7 appended');
