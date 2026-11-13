# P7/#2 — IQ carrier: restricted product construction vs literal paper IQ identification

日期：2026-11-13；abc。只读审计。

| 项 | 状态 | file:line |
|---|---|---|
| A481 受限积构造（local log-shells restricted product） | GREEN（构造） | `A481LiteralIQCarrierActual.lean:17` |
| literal `IQ(S+_{j+1}; n, D^vdash_{vQ})` 载体类型/识别 | **仍缺** | `IQCarrierFromSource.lean:6/42`（明说树内无该类型）; `LiteralIQCarrierActual.lean:6/19/96` |
| C3 侧 IQ 载体 vs 源 reduced IQ function-space packet | **缺口** | `C3IQActualPacketGapActual.lean:54` |
| C6 IQ carrier 可用但非 literal | 线索 | `ConcretePaperSignedHullActual.lean:14`; `GlobalThetaPilotIQKummerActual.lean:61` |

**结论**：#2 部分——受限积构造在 A481；literal paper IQ 载体识别缺失，不能把 A481 当 paper IQ realization。
## 更新（2026-11-13 晚）：载体复用与 FLT 依赖状态

| 项 | 状态 | file:line |
|---|---|---|
| Mathlib 自带 `RestrictedProduct` | **可用（不依赖 FLT）** | `.lake/packages/mathlib/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean:79`；我们的复用文件 `Mzk1RestrictedProductReuseActual.lean` green |
| IQ skeleton = Mathlib Πʳ | **PROVED（rfl）** | `Mzk1IQCarrierMathlibIdActual.lean`（新文件）：`IQRestrictedProductCarrier_eq`、`IQRestrictedProductCarrier_coe_mem` |
| FLT `RestrictedProduct/Equiv.lean` | **FAIL**：`:620` `dite_eq_right` unknown（pin 重命名） | `dag/watchdog/logs/tmp_external_ported_flt_FLT_Mathlib_Topology_Algebra_RestrictedProduct_Equiv.lean.log` |
| FLT `RestrictedProduct/TopologicalSpace.lean` | **阻塞**：依赖 `Equiv.olean` 不存在 | 同上 |
| FLT `FiniteAdeleRing.lean` | **SKIP**（依赖链未绿） | watchdog log SKIP records |

**结论**：literal paper IQ 仍需 `FiniteAdeleRing` 识别（FLT 修复中）；Mathlib Πʳ 的 IQ skeleton 与载体复用已完成（green）。