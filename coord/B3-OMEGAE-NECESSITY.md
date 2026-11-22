# `b3_omegaE_iso` 必要性判定页（grace，2026-11-17 12:10 CST）

问题：andrew 的 F8 第二式（`h(π(y)) = n/(n−3) h_ω(y) + O(1)`）与 F1 高度运输，
是否**确实需要**完整 unit 等式 `omegaEIsoUnit_eq`（以及 `b3_omegaE_iso`），
还是只需 frame/height 层的等式？

## 我们已有的 frame/height 层（全部 DONE，三公理）
1. `Mzk1G1B3FrameHeightActual.b3_frameHeight_omegaE_eq`（22:58:40）：
   `frameHeight n Φ (omegaYEUnit n) = frameHeight n Φ (pullbackO1Unit n)`（`n ≥ 3`）。
2. `Mzk1G1B3BundleHeightsActual.frameHeight_congr`（23:34:27）：单元相等 ⇒ frameHeight 相等。
3. `Mzk1G1B3BundleHeightsActual.frameHeight_pullbackO1_eq_pullbackOmega`（23:34:27）：
   `frameHeight n Φ (pullbackO1Unit n) = frameHeight n Φ (pullbackOmegaP1Unit n)`。
4. andrew 侧：`frameHeight_transitionUnit`（= (n−3)·logHeight₁(Φ u0)）、`frameHeight_pullbackO1Unit`（= n·logHeight₁(Φ u0)）、
   `f8_second_equality_frame`、`f8_second_equality_omegaE_frame`（23:09:52）。

## 判定
- F8 第二式的 `n/(n−3)` 正是 4 的两个 frameHeight 恒等式之比，已由 andrew 的 `f8_second_equality_omegaE_frame` 落地；
  它消费的只是 (1) 的 frame/height 等式（已 DONE）。
- 因此 **完整 unit 等式 `omegaEIsoUnit_eq` / `b3_omegaE_iso` 不是 F8/F1 的必要输入**，
  可按「J1 部分」同样方式作为**待消义务/备选**保留，不阻塞。
- 若 andrew/F1 transport 有其他消费点（例如需要 line-bundle 级 iso 去比较高度），请指出 exact 消费声明名，
  我再按 route L323 的 dt/du 每点阶数写 `omegaEIsoUnit_eq`（用已 DONE 的 `Mzk1G1B3PhiBranchActual.branch_phi_subset`
  与 B1 的 `psi_simple_zero`/`psi_unramified_over_zero` 数据），不猜公式。

## 当前 status
- `Mzk1G1B3OmegaEIsoActual`（DONE 04:04:55，三公理）：E_φ 单元层的**对象/定义部分**已绿
  （`omegaEElem`/`omegaEOverlap`/`twistUnit`/`omegaUnitExt`/`phiUnitExt`/`omegaEIsoUnit` + `_val` 引理）。
- `omegaEIsoUnit_eq`：标为**可选待办**，等 andrew 确认消费需求或 Lead 提供精确 dt/du 表述。
