# TAKKUN-DIOPHANTINE-REUSE — IUT IV §1/§2 reusable arithmetic for our two hcomp gaps

来源：`tmp/sheaf/takkun/IutLean/Diophantine/`（Takkun-IUT_LEAN 移植；对象/已验证引理可复用，其结论（含 REQUEST 的 (P)）不采纳，按待审计数据处理）。
目的：为我们 `Cor312EpsilonArithmeticComparison` 的两条唯一 named 内容缺口（Gap 1 `height_le_normalizedRegionVolume`、Gap 2 `regionVolume_le_normalizedWeight`）提供真实可用的显式算术引理。

| file:decl | 数学内容（已验证） | 对我们 hcomp 的用途 |
|---|---|---|
| `Diophantine/Thm110.lean: cTheta_ge_neg_one` | 若 `−|log Θ| ≤ C_Θ·(−|log q|)` 且 `|log q|>0`，则 `C_Θ ≥ −1`（由 Cor 3.12 的 `−|log q| ≤ −|log Θ|` 桥） | Gap 2 的 θ-pilot 常数：把 Cor 3.12 的 hull 有限性/`−|log Θ|` 界转成显式 `C_Θ` 下界；Gap 1 中 `(logVolume hull).toReal` 常数来源 |
| `Diophantine/Thm110.lean: thm110_elementary_deduction` | `l ≥ 7` 且 `(1/6)(1−12/l²)log q ≤ (1+12 d/l)D + 10(e* l+η)` ⇒ `(1/6)log q ≤ (1+20 d/l)D + 20(e* l+η)`（原论文 p.23 精确常数膨胀 12→20/10→20） | Gap 1/Gap 2 的**显式常数**：给 `(1+ε)` 归一化比较提供真实可算的系数形状（不是接口占位） |
| `Diophantine/Cor22.lean: cor22_epsilon_form` | 若 `20 d_mod ≤ ε l` 且 `20(e* l+η) ≤ ε log q`（且 adjudication test），则 `(1/6−ε)log q ≤ (1+ε)D`（l-依赖项全被 ε 吸收） | Gap 2 的 ε-归一化：把 log-volume 比较写成 `(1+ε)·weight + θbound + D` 的精确 ε-形式 |
| `Diophantine/Cor22.lean: cor22_uniform` | 存在显式 `C ≥ 0`：对所有有界不变量曲线数据与坏素数法 `N`，在 good-prime 供给假设 `hsupply` 下 `(1/6−ε)(v_q log N_v) ≤ (1+ε)D + C·N`；`C = (40·e_max·n₀+20·η_max)/ε`，`n₀=max 6 ⌈20 d_max/ε⌉` | Gap 2 的**残差常数 D**：给出 `D(ε)` 显式来源；同时指出剩余争点 = `hsupply`（good-prime 供给）与 `N ≲ 高` |
| `Diophantine/LogVolume.lean: log_two_nonneg, log_two_le_one, one_le_log_three, log_three_le_log_pi, log_pi_le_log_five, log_five_le_two` | `0 ≤ log 2 ≤ 1 ≤ log 3 ≤ log π ≤ log 5 ≤ 2` 等初等常数界 | Gap 1/Gap 2 的显式常数数值化（把 `log 2/3/π/5` 估计吸收进 `A(ε)`） |
| `Diophantine/LogVolume.lean: card_GL2 (p)[Fact p.Prime], card_GL2_two/three/five, two_mul_sum_range` | `#GL₂(F_p) = p(p²−1)` 及 p=2,3,5 显式值；组合恒等式 | Gap 2 的固定常数（`n₀`、ε-窗、局部因子界）与显式 `C` 估值 |
| `Diophantine/PrimeCountingBound.lean: theta_le` | Chebyshev θ 上界：`Σ_{p≤n} log p ≤ n·log 4` | Gap 2 中 `N`（坏素数/素因子）对数和的界，来自 Mathlib `primorial_le_four_pow`（不依赖 Takkun 结论） |
| `Diophantine/PrimeCountingBound.lean: primeCounting_le_chebyshev` | `π(n) ≤ √n + 1 + 4n/log n`（n≥2；原论文 PNT 强度的 Chebyshev 弱化版，常数略差但 ε-形式足够） | `N ≲ 高度` 估计与 Cor 2.2 素数计数的显式输入，供 Gap 2 的 `C·N` 项 |
| `Diophantine/PrimeSelection.lean: exists_prime_avoiding` | 任意 `n,N ≥ 1` 存在素数 `l ≥ n`，`l ∤ N`（可能在附加奇性/窗口选择形式下） | `l≥7`、odd、`l∤N` 的 ε-窗素数选择，Gap 2 的素数选择核 |
| `Diophantine/PrimeSelection.lean: cor22_prime_selection` | `n≥6, N≥1` 存在素数 `l ≥ max 6 n`（奇数、`l∤N`），并带窗口比较 | Gap 2 中 `cor22_uniform` 的 `l` 选择（`n₀` 由 ε 与不变量定），直接支撑 ε-抽取 |

## 使用注意 / 边界
- 全部条目只作为 **IUT IV §1/§2 的已验证算术** 复用；Takkun 的结论层（含 REQUEST (P) 与任何无条件 ABC 主张）不采纳。
- hcomp Gap 1/2 在 `Cor312ToABCBridgeInterface` 中是 `IQHullLogVolumeInterface` 的 `ENNReal.toReal` 形式；上述常数是 `ℝ` 形式，接线需一条 `toReal` 换算引理（下一步写名为 `hcomp_ennreal_toReal_constants` 的适配引理，仅算术换算，不含未证内容）。
- `thm110_elementary_deduction`、`cor22_epsilon_form`、`cor22_uniform` 的假设（`AdjudicationTest`/`hsupply`/`l ≥ 7` odd 等）都是 Takkun 模型内的具名命题；复用前须逐条核对其定义是否与我们的对象（q-pilot/Theta-pilot、literal carrier）语义一致，不一致则只取其**常数不等式**部分。
- 当前唯一 named 内容缺口仍为 `abcbridge:Cor312EpsilonArithmeticComparison.twoNamedGaps`（Gap 1/2）；本清单是支撑材料，不构成证明。

## A500 Takkun 对象层盘点（IutLean 67 文件）

| 目录 | 文件数 | 代表模块（对象层） |
|---|---|---|
| (root) | 2 | Basic.lean, Models.lean |
| Anabelian | 6 | Anabelian/Core.lean, Anabelian/CoreData.lean, Anabelian/CurvePi1.lean, Anabelian/CyclotomicRigidity.lean, Anabelian/FundamentalSequence.lean, Anabelian/Tempered.lean |
| Arithmetic | 8 | Arithmetic/AdjudicationTest.lean, Arithmetic/CurveInstance.lean, Arithmetic/ExamAttempt.lean, Arithmetic/IntegrationTest.lean, Arithmetic/PilotDegrees.lean, Arithmetic/RealFrobenioid.lean, … |
| Cohomology | 3 | Cohomology/CentralExtension.lean, Cohomology/Continuous.lean, Cohomology/Synchronization.lean |
| Combinatorics | 1 | Combinatorics/Fl.lean |
| Cyclotome | 2 | Cyclotome/Frobenius.lean, Cyclotome/Kummer.lean |
| Diophantine | 6 | Diophantine/Cor22.lean, Diophantine/LogVolume.lean, Diophantine/PrimeCountingBound.lean, Diophantine/PrimeSelection.lean, Diophantine/Szpiro.lean, Diophantine/Thm110.lean |
| EllipticCurve | 4 | EllipticCurve/FieldOfModuli.lean, EllipticCurve/GaloisRep.lean, EllipticCurve/Reduction.lean, EllipticCurve/Torsion.lean |
| Foundations | 1 | Foundations/Cyclotome.lean |
| Frobenioid | 3 | Frobenioid/Basic.lean, Frobenioid/PrimeStrip.lean, Frobenioid/PrimeStripSystem.lean |
| HodgeTheater | 3 | HodgeTheater/Defs.lean, HodgeTheater/PrimeStripData.lean, HodgeTheater/Symmetry.lean |
| InitialThetaData | 2 | InitialThetaData/Deferred.lean, InitialThetaData/Defs.lean |
| LogTheta | 5 | LogTheta/Indeterminacy.lean, LogTheta/Lattice.lean, LogTheta/LatticeConcrete.lean, LogTheta/LogKummer.lean, LogTheta/LogShell.lean |
| Multiradial | 8 | Multiradial/Cor312.lean, Multiradial/DisputedCore.lean, Multiradial/IdentificationAudit.lean, Multiradial/MainTheorem.lean, Multiradial/ThetaHullDichotomy.lean, Multiradial/Thm311.lean, … |
| NumberTheory | 3 | NumberTheory/DifferentBound.lean, NumberTheory/PlaceLocalization.lean, NumberTheory/Places.lean |
| Padic | 7 | Padic/ComplexLog.lean, Padic/LogShellRadius.lean, Padic/LogVolume.lean, Padic/PadicExp.lean, Padic/PadicLog.lean, Padic/RealLogKummer.lean, … |
| Theta | 3 | Theta/MonoTheta.lean, Theta/ThetaGroup.lean, Theta/ThetaValues.lean |

### promachina（vendor/promachina，9823 .lean）
- 体量巨大（含对 Mathlib 的 vendor 快照）：本轮**未整体采纳**；只作为对象定义/已验证引理的检索源，遇到需要时按 file:decl 逐条登记并审计，不把其 REQUEST/结论当作证据。

### 保真审计要点（hcomp/(P) 对齐）
- Takkun 算术层（上表）可复用的是**显式常数不等式**；其 `PilotVolumeData`/`ArithmeticData`/`AdjudicationTest` 是 Takkun 自有对象，与我们 literal carrier/`LiteralCarrierAxiomsV3` 的语义**尚未逐项对齐**，不能直接把 `cor22_uniform` 的假设当我们的 hcomp；须先写语义桥（对象字段 → 我们的 logVolume/height）。
- `REQUEST` 的 (P) 与任何无条件结论按待审计数据处理，不构成 hcomp Gap 1/2 的证明。