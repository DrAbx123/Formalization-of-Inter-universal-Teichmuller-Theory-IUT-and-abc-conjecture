# Context Goal Check（目标/证据检查）

- Goal: `goal-9baa9641-5902-46a4-87f0-1430e6005d13` (revision 12, phase active)
- Objective: 从基础三公理无条件构建 IUT 3.12、IUT IV Thm 1.10、abc；禁止 sorry/额外 axiom/toy；维护审计与编译 gate；所有编译走 watchdog。
- Lean 检查文件: `tmp/sheaf/xif/paper/Mzk1ContextGoalCheckActual.lean`
- watchdog 目标: 已加入 `dag/watchdog/extra-targets.txt`

## 检查内容
该 Lean 文件只做 `#check` / `#print axioms`，不证明目标本身：

1. 3.12 条件目标: `Mzk1ActualRamifiedDataActual.actual_paper312`
2. IV Thm 1.10 条件 display: `Mzk1IVThm110Actual.thm110_display_of_hCor312`
3. hSlack derived 接口: `S3171...Thm110DisplayInputsOfCor312`
4. abc 条件消费者: `Mzk1Cor312ToABCConsumerActual.abcConjecture_of_namedInputs`
5. hθ unit-lattice 单向界: `Mzk1ThetaUnitLatticeBoundActual.unitLatticeLogVolume_le_thetaHull`
6. stage4 valueGroup: `Mzk1GaloisCompletionActual.valueGroup_comap_eq`
7. Qp 范数归一化: `Mzk1PadicFieldValuedQpActual.padicField_v_eq_valuation`

## 解释
- 这些是**检查目标接口和 donor 存在性**的声明，不是无条件证明；
- 若任一 #check 失败，按 watchdog FAIL 日志修；
- 若 #print axioms 出现 sorryAx 或额外公理，对应文件不接受。

## 当前已知仍缺
- R1 single-local q vs global q family；
- hq 的 `qVEffectiveMultiplicity → RamifiedPlaceData.mult` index map；
- hθ 的 unit-lattice positivity/finiteness（`hpos/hfin`）；
- stage4 `UniformContinuous`/`Completion.mapRingHom`；
- SG3b、A2、WQuotient、abc Undilated bounds。
