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

## 8. 更多外部文献（2026-11-14 第二轮搜索，均“登记/备用”，当前主链不消费）

| 主题 | 文献/来源 | 说明 |
|---|---|---|
| Serre mass formula | Serre 1978 (C. R. Acad. Sci. Paris A286, 1031–1036)；UCL thesis 转引 `m̃(Êt_{1^n}/F)=1/q_F^{n-1}`；TauCeti LocalFieldScaling 亦以此为例 | 与 unitMass/局部体积归一化相关，当前只需 class-B 层不消费 |
| Faltings height 比较 | Silverman 高度比较估计（Pila 转引：`|h(x)-12h_F(E)|` 界） | 旧 E7 L2 用；signed 链不用 |
| Néron period | 现代文献（如 arXiv 2412.16629 引 DD15 Lemma 2.4；Zenodo BSD 文）`Ω_E^±` 最小模型/同源/二次扭唯一确定 | 旧 E7 L8 用；登记 |
| Petersson 范数估计 | Fomenko 显式估计（zbMATH Zbl 04128909）；Kramer sup-norm notes Thm 4.4 | 旧 E7 L7 用；登记 |
| Artin–Whaples product formula | 标准（反问题刻画 product formula） | 当前 B5 用 Mathlib `NumberField.prod_abs_eq_one`（内部） |

## 9. IUT 3.12 相关外部分析（**注意：不是可引用定理，只是文献/语境**）
- Zenodo 上有若干对 IUTchIII Cor 3.12 缺口/“validation”的分析与争论文章（如 *The Gap in IUTchIII, Corollary 3.12: From Attempted Repair to Structural Diagnosis*；*A Validation of IUT: The Contested Bound, Instantiated from Source*；*A LOCAL NON-CONTAINMENT IN STEP (V) OF IUT IV*）。这些是评论/争议文献，**不能作为 class-B 数学输入**，仅登记供语境参考；外部共识仍是 abc 未被证明。
- 结论：没有外部定理能直接替代当前 signed Cor312 的比较不等式；唯一已发现可立即消费的外部机器验证结果是 TauCeti 的 p-adic Haar 缩放律（见 §7）。

### Cor 3.12 的精确外部陈述（Dupuy–Hilado，已 fetch ar5iv HTML 全文）
- T. Dupuy, A. Hilado, *The Statement of Mochizuki's Corollary 3.12: Initial Theta Data*（arXiv:2004.13228；原题含 First Two Indeterminacies）。
- 精确不等式（1.1）：`−deĝ(P_q) ≤ −deĝ_lgp(P_hull(U_Θ))`；`U_Θ = Ind2·(Ind1·(O_L(−P_Θ))^{Ind3})`（1.2）。
- 关键澄清：**log-volume 不是体积对数，而是归一化 p-adic/arch Haar 测度对数的加权平均**：`lnν_{L_p}(A_p) = E( ln μ_v(A_v) / dim L_v )`，再对 p 求和；`lnν_L(hull(U_Θ)) = −deĝ_lgp(P_hull(U_Θ))`。
- 该文只给出陈述与 initial theta data 可计算性，**不给 Cor 3.12 的证明**；可用于校准我们的 native readout 归一化（除维数、p-平均、Ind/procession 平均）。
- 结论：体积下界（route C0 已证 `μ(Q_root) ≤ μ(H_root)`）必须先经过上述归一化识别才能变成 `log q ≤ theta` 比较；没有外部定理可跳过这一步。

## TauCeti port 状态（2026-11-14，qpilot）

- 复制的 10 个文件在 `tmp/sheaf/xif/paper/TauCetiPort/TauCeti/...`，import 已改为 `tmp.sheaf.xif.paper.TauCetiPort.TauCeti.…`。
- GREEN 4/10：`RingTheory/DiscreteValuationRing/Basic`、`Data/Int/WithZero`、`RingTheory/Valuation/AbsoluteValue`、`RingTheory/Subring/SpanSingleton`。
- 精确 API 缺口（Lean 4.32 vs 4.36）：`RingTheory/Valuation/Discrete/Order.lean:114` 需要 `v.IsRankOneDiscrete`，4.32 中 `IsRankOneDiscrete.mk'` 需显式 `[IsCyclic (valueGroup v)]`；port 仅带 `[Nontrivial (valueGroup v)]`。
- 决策：按 Lead 指示不无限投入；保留 class-B 外部 `PAdicHaarDetScaling`（`Mzk1PAdicHaarDetScalingExternalActual`）作为 det-Haar/#10 的可用支撑；TauCeti port 记为“部分移植：4/10 green + Order 精确 API 缺口”。
- 若后续补 Mathlib 4.32 的 `IsCyclic valueGroup` 局部实例，可继续 port。

### 20.2 TauCeti port 决策（2026-11-14 12:10）
- port 状态：**4/10 green**（DVDRing/Basic、Int/WithZero、Valuation/AbsoluteValue、Subring/SpanSingleton）；6 pending。
- 真 API 缺口：`TauCetiPort/.../RingTheory/Valuation/Discrete/Order.lean:114` 需 `[IsCyclic (valueGroup v)]`（4.36 隐含实例，4.32 缺失）⇒ 按 Lead 决定**停止无限投入**，保留 class-B 外部 `PAdicHaarDetScaling` 支撑 det-Haar/#10，port 记为“部分移植 + 精确 API 缺口”。
- det-Haar 继续走 class-B：MatrixSplit/DiagonalNorm 修复后接 `detHaar_map_of_factors`；内部 SNF 路线保留为交叉校验。

### TauCeti port 最终判定（1–2 波时间盒后冻结，2026-11-14）

- 4/10 green；其余阻塞在 CardQuotient 的 **4.36 广义定理**
  Ideal.cardQuot_mul（无 Module.Free ℤ R）在 4.32 不可用：
  4.32 版本强制 [IsDedekindDomain S] [Module.Free ℤ S]，
  而局部域整数环 O[K] 不是有限自由 ℤ-模。
- 这不是“补一个 instance”可修：需重证 DVR/Dedekind 情形下不依赖 Free ℤ 的理想商基数乘性，超出时间盒。
- 决策：冻结 port；保留 class-B Mzk1PAdicHaarDetScalingExternalActual（已 green）
  支撑 det-Haar/#10；TauCeti port 记录为“4/10 green + CardQuotient 广义定理缺口”。

## StepVAssembly 供体与 Box (11) 精确引用（2026-11-14，qpilot）

- Lean 供体：`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean`
  - `arithmeticTuple_stepV_normalizedLogVolume_le_paperBound`
  - olean GREEN（1.84MB）
- 新 Box 文件：`tmp/sheaf/xif/paper/Mzk1IutIVProp14iiiBoxFormalActual.lean`
  - `prop14iii_box_formal`
  - 输出：μ_log(S) ≤ (-ord_p(varpi) + Σ_i ord_p(δ_i) + 1) log p + Σ_{i∈I*}(3+log e_i)
  - 不 import Iut/TFG；Iut 104 文件闭包已放弃
- consumer：`Mzk1IutIVProp14iiiBoxConsumerActual.lean`
  - `S1915BoxConsumer` 显式记录 S1915 hull 与 StepV tensor 的 carrier 桥
  - `s1915_a0_le_box` 由 `prop14iii_box_formal` 得 S1915 a0 ≤ Box
- 假设来源：Φ 为 Ind1/Ind2 保 `arithmeticTupleUnitLogLattice` 的线性自同构族；
  varpi 为 distinguished factor 的非零元素；exceptional 为 e_i>p-2 的因子集。
- 未完成：S1902Carrier 与 ArithmeticTensorTupleBlock 的**具体** carrier 等价（consumer bridge 目前是显式字段，不是已证等式）。
