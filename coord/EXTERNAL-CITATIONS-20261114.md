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

## 7. 精确文献核验（2026-11-14，new Web Search/Fetch API 已启用）

### Mestre–Oesterlé 1989 的准确陈述（zbMATH 评论原文）
- Zbl 0693.14004 评论（Reviewer: E.-U. Gekeler）：
  - **Theorem 1**：若 E 是 Q 上半稳定 Weil 曲线，且 `|Δ|` 是 m 次幂，则 `m ≤ 5`，且 E 有 Q-有理的 m-除点（m-division point）。
  - **Theorem 2**：若 E 的导子为素数 p，则（有少量明确列出的例外）最小判别式 `Δ = ±p`。
  - 证明用 Ribet [Invent. Math. 100 (1990) 431–476] + Serre [Duke Math. J. 54 (1987) 179–230]；逐一排除 m 被 7,10,15,6,9,25,8 整除 ⇒ m≤5。
  - 定义：Weil curve = 存在非平凡 Q-态射 `X_0(N) → E`（模性）。
- 来源：`https://zbmath.org/?q=an%3A0693.14004`（评论全文，已 fetch）；Semantic Scholar 摘要 `https://www.semanticscholar.org/paper/...`（法文摘要：m≤5 + 有理 m-除点；素数导子 Δ=±p）。
- **重要更正**：项目代码里 `MestreOesterleBound (logq logd C) := logq ≤ 6·logd + C` 是**归一化 Szpiro-6 形状的替代输入**，不是 Mestre–Oesterlé 原文定理；原文定理是上面的 Thm 1/Thm 2。最终形式化 MO 时必须用 Thm 1/2，并把归一化不等式改名为 `Szpiro6Shape` 或从 Thm 1/2 推导。

### p-adic Haar det 缩放律：已有 Lean 机器验证（TauCeti）
- 本地 `tmp/TauCeti/TauCeti/MeasureTheory/Group/LocalFieldScaling.lean`（上游 github.com/TauCetiProject/TauCeti，Lean 4.36，本地未编译）包含：
  - `MeasureTheory.Measure.measure_image_mulVec_integerBox`：对 O_K-整数矩阵 A，`det A ~ ϖ^k`，则左不变测度下 `μ (A '' integerBox) = q^(-k) μ(integerBox)`；
  - **`MeasureTheory.Measure.addHaar_image_mulVec`：对 Haar 测度 μ 和任意集合 s，`μ (A '' s) = q^(-k) · μ s`**（即 p-adic Haar det 缩放律的一般形式）；
  - 依赖闭包仅 10 个 TauCeti 文件（~110KB），可移植到本项目（Lean 4.32.2）。
- 文档：`https://taucetiproject.org/docs/TauCeti/MeasureTheory/Group/LocalFieldScaling.html`。
- **行动**：qpilot 负责把这 10 个文件移植为 `tmp/sheaf/xif/paper/TauCetiPort/...` 模块并让 watchdog 编译；成功后 `PAdicHaarDetScaling` 由 ported `addHaar_image_mulVec` 直接证明，GAP-DET-HAAR 从“class-B 外部输入”升级为“内部 ported 证明”。若移植遇 4.32 vs 4.36 API 差异，报告精确首个错误/API，回退保持外部输入。
