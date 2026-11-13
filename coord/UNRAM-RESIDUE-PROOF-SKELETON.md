# UNRAM/RESIDUE 实际证明骨架（FLT BaseChange 就绪后）

日期：2026-11-13 08:10。Status: BLOCKED ON FLT OLEAN；本文件是证明骨架，不是已证声明。

## 0. 当前阻塞
- tmp/external/ported/flt/FLT/DedekindDomain/Completion/BaseChange.lean 仍无 olean，watchdog 最后 FAIL；
- 因此 inertiaDeg_eq_inertiaDeg（BaseChange.lean:718）与 ramificationIdx_mul_inertiaDeg_eq_finrank（:751）当前不可 import；
- 已 green 的 FLT 文件：IntegralClosure.lean、AdicValuation.lean（ole 存在），但不能替代 BaseChange 的局部/全局比较。

## 1. 目标
证 nativeBadLocalWeight T b = 1，条件是：
- relativeRamificationIndex (nativeBadToKPlace T b) = 1；
- relativeResidueDegree (nativeBadToKPlace T b) = 1；
- 现有 GAP-PC-FINITE / GAP-PC-AGREE 输入（见 Mzk1P3WeightDegreeOneActual）。

## 2. 已证可复用
- relativeCompletionDegree_eq_one_iff：e*f=1 ↔ e=1 ∧ f=1；
- nativeBadLocalWeight_eq_one_of_unram_residue：FINITE + AGREE + e=1 + f=1 ⇒ nativeBadLocalWeight=1（Mzk1P3WeightDegreeOneActual:54）；
- localResidueDegree/relativeResidueDegree 定义相同：(comap place).maximalIdeal.asIdeal.inertiaDeg' place.maximalIdeal.asIdeal；
- Mzk1C17ResidueFieldEquivActual：residue-field algebra equivalence ⇒ inertiaDeg'=1。

## 3. FLT BaseChange 绿后的精确证明步骤
1. import tmp.external.ported.flt.FLT.DedekindDomain.Completion.BaseChange；
2. 对 w = nativeBadToKPlace T b：
   - 用 inertiaDeg_eq_inertiaDeg（BaseChange:718）把局部 inertia degree 与全局 w.1.asIdeal.inertiaDeg 对齐；
   - 用 ramificationIdx_mul_inertiaDeg_eq_finrank（:751）与全局目标 ramificationIdx=1/inertiaDeg=1 得到局部 e=f=1；
3. 用 relativeCompletionDegree_eq_one_iff 得 relativeCompletionDegree=1；
4. 用 nativeBadLocalWeight_eq_one_of_unram_residue 得 weight=1。

## 4. 仍需的算术输入（不可由 FLT 推出）
- 全局 ramificationIdx = 1（即 eSource=1 的 bad place 情形）；
- 全局 inertiaDeg = 1（即 localResidueDegree=1）；可由 ResidueFieldEquiv 充分条件供给，但实际同构未构造。

## 5. 下一步
- 先让 BaseChange.lean 在 watchdog 转绿（当前 FAIL，按 per-file log 修 API 漂移）；
- 绿后新建 Mzk1C17UnramResidueBridgeActual.lean，只做上面的 FLT 实例化，不新增假设。