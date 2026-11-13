# P7/NORM-ARCH-C 余项 — hArc ↔ Cor312ComparisonGap 字典尝试（GAP）

日期：2026-11-13；abc。

| 已证 | file:line |
|---|---|
| `heightWeight_rat/toricHeightWeight_rat`（ℚ arch 因子 =1 / 1/2） | `Mzk1NormArchCAbcActual.lean`（green，watchdog DONE 22:13:45Z） |
| `hArc_rat/hToricArc_rat/hNon_rat`（ℚ 展开为无权和） | `Mzk1NormArchCHArcActual.lean`（green，DONE 22:16:31Z） |
| degree-one 条件式 `hArc_eq_sum_of_finrank_one` / `hToricArc_eq_half_mul_sum_of_finrank_one` | 同上 |
| `archFactor_eq_one_of_finrank_one` / `toricArchFactor_eq_half_of_finrank_one` | `Mzk1ArchFactorDegreeOneActual.lean`（本批新文件） |

## 剩余缺口

```
GAP-NORM-ARCH-C-K：ABC route 无显式 K/[K:Q] 实例；只有 ℚ 语句（ABCBridge/Statement.lean:26/28）。
GAP-NORM-ARCH-C-COR312：hArc/arch 项到 Cor312ComparisonGap 的字典未构造；
  Cor312 比较使用 S2717/S3137 的 log-volume 读数，IUT IV heightWeight 进入 hArc/hBox，
  两者之间的 arch 项等式（乘 1/[F:Q] 后）无实际定理；本批只完成 ℚ/degree-one 归约。
```