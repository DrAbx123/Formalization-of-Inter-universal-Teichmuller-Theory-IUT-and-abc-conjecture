import { appendFileSync, readFileSync, existsSync } from 'node:fs';
const ROOT='D:/lean';
const prio=readFileSync(ROOT+'/dag/watchdog/priority-files.txt','utf8').split('\n').filter(Boolean);
const olean=f=>existsSync(ROOT+'/.lake/build/lib/lean/'+f.replace(/\.lean$/,'.olean'));
const green=prio.filter(olean).length;
const add=['','## 8. fresh 日志迭代（A484 本轮）','','- priority 44 条: green='+green+'（较上轮 +3）；queue=444。fresh logs(12min)=43 条，其中多数为 owner 正在修改的文件（src_mtime 晚于 logtime）的 stale 失败。','- 典型 stale 模式: Mzk1R4LiteralAssemblyActual（mainline, mtime 20:37）、Mzk1QPilotSHEDoubleImageActual（qpilot, mtime 20:41）、A483LiteralCarrierProductHaarActual（abc, mtime 20:33，当前版本已 import SourceOriginalInput/PadicLogShellModel，log 为旧版错误）。','- 根因说明（供 owners 参考）: OriginalInput 是 LeanFormal.IUT.Theorem311Source.OriginalInput（SourceOriginalInput.lean），未 import/open 时会被 autoImplicit 当局部变量，导致 invalid use of explicit universe parameters；SourcePilotRegionData 在 LeanFormal.IUT.N8Closure.SourcePilotRegion。A483 当前版本已含正确 import，无需再修。','- 行动: 本轮无新增/修改文件、无新增队列条目；继续按 fresh 日志确认 owner 修复后的重编结果。',''];
appendFileSync(ROOT+'/coord/A484-RUNG-QUEUE-AUDIT-shehdd.md', add.join('\n'));
console.log('addendum 8 appended; priority green='+green);
