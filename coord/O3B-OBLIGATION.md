# O3(ii)(b) 显式义务：scheme 层 `Branch (hPoly h hh) ⊆ boundarySetGlued`
（grace，2026-11-17 13:05 CST）

## 义务陈述（不含任何伪装闭合）
目标：对 `h : Polynomial ℚ`、`hh : h ≠ 0`，在 B1 的解析输入（`M2AnalyticTarget` 第三合取）下证明
```lean
Branch (Mzk1G1PsiHPolyFinalActual.hPoly h hh) ⊆ boundarySetGlued
```
其中 `Branch f := f '' Ram f`（`Mzk1G1BelyiRamificationActual`，LANA port，DONE 23:24:10），
`boundarySetGlued = p1Zero ∪ p1One ∪ p1Infinity`。

## 已有输入
- 值层（DONE 04:35:08）：`Mzk1G1B1O3ValueLayerActual.o3a_aeval_of_derivative_zero` 与
  `o3a_criticalValues_subset` —— 导数零点处的值在 `{0,1}`（来自 `M2AnalyticTarget` 第三合取）。
- 归约（emmy，DONE 04:46:11，`Mzk1G1B1HbObligationsActual`）：
  `branch_hPolyL_subset`（`Branch(hPolyL) ⊆ p1Inv '' Branch(hPoly) ∪ Branch p1Inv`）、
  `branch_p1Inv_empty`、`hb_of_branch_hPoly_subset`、`hbH_iff_branch_hPoly_subset`。
  ⇒ O2/hb 精确归结到本义务。
- `hPoly` 的 chart 数据：`Mzk1G1PsiHPolyFinalActual`（`hPoly_ι_c0/c1/c2`、`hPolyCover`）与
  `Mzk1G1PhiFixedLChartInfBoundaryActual.chartMorphismInf_comp_hPoly`（t-chart 公式）。

## 缺口（真缺口，树内无 donor，emmy 亦确认）
缺少 **`hPoly` 的分歧描述**：`Ram (hPoly)` 需要 `hPoly` 的 chart 层导数/形式光滑性计算
（对应 route 'P′Q − PQ′ / ∞ 图 t=1/z 的局部公式'）。现有件只给 `hPoly` 的 chart 映射与
boundary 判定，没有 `Ram`/`smoothLocus` 的逐点描述。

## 可行路线（供后续排期）
1. 在 chart0 片用 `hPoly_ι_c0` 与 `chartMorphism0` 的点公式，把 `hPoly` 的局部形式写成
   `Spec ℚ[λ] → Spec ℚ[t]`（t = h(λ)），再用 `Ram` 定义（stalk 形式光滑性）与
   `Polynomial.derivative` 的非零性做逐点判定；
2. ∞ 片用 `hPoly_ι_c2` 的 t-chart 公式（`chartMorphismInf_comp_hPoly`）；
3. 用值层结果把分歧值落到 `{0,1}`，完成 `Branch hPoly ⊆ boundary`。

## 状态
- O3(i)（`φ^*O(1) ≅ L^{⊗d}`）DONE（`b3_pullbackO1_iso`，23:44:37）。
- O3(ii)(a) 值层 DONE（04:35:08）。
- O3(ii)(b) 本页 = OPEN，owner grace；不阻塞 F8/F1（`b3_omegaE_iso` 为可选义务）。
