# 外部定理引用清单（2026-11-14，Lead web 调研）

说明：本地 web_fetch 对多数出版站点被 DNS/网络策略拦截（zbmath.org/semanticscholar/doi.org 均解析到非公开 IP），只能拿 web_search 摘要；下列条目除已核来源外均标注 **待原文核对**。

## 1. Mestre–Oesterlé 1989（E7/EMO）
- J.-F. Mestre, J. Oesterlé, « Courbes de Weil semi-stables de discriminant une puissance m-ième », J. Reine Angew. Math. **400** (1989) 173–184；zbMATH **Zbl 0693.14004**（搜索命中 `https://zbmath.org/?q=an%3A0693.14004`）；DOI `10.1515/crll.1989.400.173`。
- 状态：元数据已核；**定理精确陈述（例外素数、导子条件、指数界）仍未逐字核验**（见 `coord/E7-SOURCE-AUDIT.md`）。
- 已消费位置：`Mzk1DExactLowerActual`（D_exact 下界）、`Mzk1P3FinalAssemblyActual`（`ssIneqExplicit`）、`Mzk1P3DictDOrdInterfaceActual`（`C.e≤5`）；`Mzk1MestreUseWiringActual`（class-B 接线，4 定理）。

## 2. p-adic Haar 测度的线性变换缩放律（对 GAP-DET-HAAR 直接可用）
**陈述（标准定理，待引用原文）**：E 为有限维 ℚ_p 向量空间，μ 为 Haar 测度，f : E ≃ₗ[ℚ_p] E 为 ℚ_p-线性自同构，则存在常数（模）c = ‖det f‖_p，使得 `μ (f '' S) = c · μ S` 对所有 Borel S 成立。等价地 `μ.map f = ofReal ‖det f‖ • μ`。
- 文献：A. Weil, *Basic Number Theory*（Springer；locally compact 域的 Haar 测度与模）；Bourbaki, *Intégration* VII（Haar 测度）；J. Igusa, *An Introduction to the Theory of Local Zeta Functions*（p-adic Haar 归一化/缩放的标准用法）；也可引 Folland, *A Course in Abstract Harmonic Analysis* 的模函数/Haar 测度章节。
- **用途**：直接替代 GAP-DET-HAAR 的 matrix-level SNF + diagonal factor 两步（把外部标准定理作为 class-B 输入），随后再形式化陈述。
- 待办：把它写成显式 Prop（`PAdicHaarDetScaling`），由 qpilot 接线到 `detHaar_degree_scaling_eq_ofReal`。

## 3. 局部域归一化绝对值的延拓（对 P2 q 读数可参考）
- 标准：Neukirch, *Algebraic Number Theory* II；有限扩张的归一化绝对值限制回基域（`‖algebraMap x‖ = ‖x‖` 的适当归一化）。项目里已有 `norm_algebraMap'` 等内部供体，**当前不需要外部输入**。

## 4. Tame different 指数 e−1（residue-one 相关）
- 标准：Serre, *Local Fields*（tame ramification）；项目已有 `LeanFormal/IUT/IUTIV/Estimates/DifferentTameEquality.lean`（e−1 精确指数），故 residue-one 不需要外部定理，只需 paper tame/split 输入。

## 5. 旧 §12.2/E7 其它外部输入（当前主链不用，登记备用）
| 名称 | 文献 | 状态 |
|---|---|---|
| Faltings height bound | Faltings 1983；Silverman *Heights* | 待核 |
| Ribet–Takahashi | Ribet 1990 level-lowering；Takahashi | 待核 |
| Petersson asymptotic | 经典 Petersson/Michel–Ullmo 类估计 | 待核 |
| Néron period lower bound | Pellarin 类显式公式 | 待核 |
| optimal quotient | Mazur/Ribet–Takahashi | 待核 |

## 6. 结论
- 当前活跃链可直接消费的外部定理：**p-adic Haar det 缩放律**（关闭 GAP-DET-HAAR 的最后两步，条件：接受外部标准定理作为 class-B 输入，最后形式化）。
- Mestre–Oesterlé 已按判定表在旧 §12.2 消费；当前 signed/native 链不消费它。
- 其余外部定理仅影响旧 E7 路线；不影响当前 P0–P4。

## p-adic Haar determinant scaling (class B, added 2026-11-14)

Statement: for a finite-dimensional Q_p vector space E and a continuous Q_p-linear automorphism f, every additive Haar measure mu satisfies

  mu.map f = ENNReal.ofReal (norm (det f)) * mu.

Sources: Weil, *Basic Number Theory* (Haar measure on local fields); Bourbaki, *Integration*; Igusa (p-adic integration).

Lean file: `tmp/sheaf/xif/paper/Mzk1PAdicHaarDetScalingExternalActual.lean`
- `PAdicHaarDetScaling` : explicit Prop, class-B input (no fake proof)
- `detHaar_degree_scaling_of_external` : direct consequence
- `detHaarSNFReplacedByExternal` : SNF route retained as internal cross-check, not a gap

Last formalization TODO: connect this external law to the concrete Haar normalization used in S3137/P3 consumers (same exact statement, different measure instance).
