# KAPPA-CORIC-AUDIT — 我们仓库的 κ/coric 现状审计（只读）

日期：2026-11-12；qpilot（A914）。审计范围：`LeanFormal/` 与 `tmp/sheaf/xif/paper/` 中所有 κ/coric 相关定义；对照 IUT I Example 5.1(v)。**未跑 Lean 全量 gate（除 S1388 自带 `#print axioms` 探针）；olean 存在性单独列出。**

## 0. 结论（先给）

**没有任何对象能给出「κ-coric 函数在各位的赋值/范数」。** 仓库里的 κ/coric 对象只有三类：
1. **KappaOrbit / Kummer 同构数据**（`SourceKappaOrbit*`、`KappaOrbitPairActual` 等）：它们记录 `O^{×μ}(G) ≅ O^{×μ}(A)` 的**同构/轨道**，但 `sourceUnits` 是 frozen interface（任意类型 + 群作用），**没有赋值 `ord_v`、没有 arch 范数、没有线丛截面**；
2. **coricModule/coricKummerLink 的抽象层**（`Kummer/*`）：`coricModule` 是任意 `Type`（如 `ℂ`、`D.M`、`D.K`），`coricKummerLink` 是 `Prop` 关系；**不是 κ-coric 函数**，只是 vertical Kummer upper-semi 的抽象模型；
3. **paper 的 kappa 构造尝试**（`S1388/S1399/S1425/S1959` 等）：实际构造了 source units / pair datum / reduced coric vertices，但**文档明确声明** paper 的 `O^{×μ}(G)` 算法、`κ^×μ` 同构、F^⊩ carrier、κ-coric functions 均缺失；`KappaOrbitPair/LinkedKappa/LowerKappaDonor` 还有 `Missing*` 接口且 olean=false。

**因此 face5 S3（κ-coric 截面候选）不成立；必须补 IUT I Example 5.1(v) 的 κ-coric 层，或把它登记为显式外部假设（class-B）。**

## 1. 审计表（定义/定理、内容、olean/gate、Missing/conditional）

### 1.1 LeanFormal：KappaOrbit（`IUTII/Frobenioid/SourceKappaOrbit*`）

| 文件/对象 | 定义/定理 | 内容 | olean | gate/Missing |
|---|---|---|---|---|
| `SourceKappaOrbitFactorizationProvider.lean` | `evaluationFactorization`, `piTupleHom`, `universalKappaOrbitUnitsActionDatum`, `pairFactorizationUpper/Lower`, `pairUnitsActionUpper/Lower`, `kappaOrbitFactorizationProvider : Obligation` | 每 strip/每 place 的 factorization `G →* toDPrimeStrip.Pi v` + orbit 数据，供给 `KappaOrbitUnitsActionDatum` | ✅ true | 源级无 sorry/axiom；**conditional**：`Obligation` 是接口，group-theoretic algorithm 未构造 |
| `SourceKappaOrbitUnitsActionSupply.lean` | `KappaOrbitUnitsActionDatum`（fields `sourceUnits : V→Type`, `sourceAction`, `factor`, `kappa`）；`suppliedUnitsAction`、`kappa_equivariant`、`kappa_invariantImage`、`kappa_transports_action`、`representativeDifference`、`canonicalDatumOfFactorization` | `O^{×μ}(G) ≅ O^{×μ}(A)` 的 orbit 代表与 invariant-image 律；`sourceUnits` **frozen interface**（§doc L43–45 明说 algorithm 未构造） | ✅ true | 源级无 sorry/axiom；conditional on interface；canonical completion 是 identity（gate-only） |

### 1.2 LeanFormal：Kummer 的 `coricModule`/`coricKummerLink`

| 文件/对象 | 定义/定理 | 内容 | olean | Missing/conditional |
|---|---|---|---|---|
| `Kummer/VerticalLogKummerOrderedLayer.lean` | `NonarchimedeanLogKummerUpperSemi`（`coricModule : Type`, `logShell : Set coricModule`, `kummer : ∀ m, Unit m → coricModule`, `coricKummerLink : coricModule → Unit m' → Prop`）；`ArchimedeanLogKummerUpperSemi`（`coricModule`, `archimedeanBall`, `piBallImage`, `coricKummerLink`）；`VerticalLogKummerOrderedLayer` | vertical log-Kummer upper-semi 的抽象层；`coricKummerLink` 是 **Prop 关系**，不是函数/赋值 | ✅ true | 无；但**不是 κ-coric 函数** |
| `Kummer/MonoAnalyticLogShellArchPsiCnsCalibration.lean` | `coricModule := ℂ`, `coricKummerLink := fun _ _ s a => s = signFactor a`；`archimedeanLogKummerUpperSemiSignCalibration` | archimedean sign calibration；`coricModule` 取 `ℂ` | ✅ true | 无；与 IUT I κ-coric 无关 |
| `Kummer/MonoAnalyticLogShellCompactCarrier.lean` | `MonoAnalyticLogShellCompactCarrier`（`coricModule := D.M`, `preLogShell`, `logShell`, `unitLayer`, `codomainKummerContained`） | 抽象 log-shell container；`coricModule` 是 `D.M` | ✅ true | 无；非 κ-coric |
| `Kummer/SourceLogShellCarrier.lean` | `SourceLogShellDatum`（`coricModule := D.K`, `preLogShell`, `logShell`, `unitLayer`） | 局部域载体 + log-shell；`coricModule := D.K` | ✅ true | 无；非 κ-coric |
| `Kummer/SourceK1K2ArchUpperSemiBridge.lean` | `ArchimedeanLevelSurjectionShape (Unit) (coricModule) ...`、`archimedeanLogKummerUpperSemiSignCalibration.coricModule` | arch upper-semi 形状，参数化 `coricModule` | ✅ true | 无；非 κ-coric |

**共同点：`coricModule` 只是任意 Type/具体载体，`coricKummerLink` 是 `Prop`；没有任何 `κ-coric` 函数的逐位取值/范数。**

### 1.3 paper：kappa/coric 相关文件

| 文件 | 定义/定理 | 内容 | olean | Missing/conditional |
|---|---|---|---|---|
| `KappaOrbitPairActual.lean` | `LowerKappaDonor`（`∀ v, TimesMuKummer.Isomorphism (pairUnitsActionUpper…) (pairUnitsActionLower…)`）、`pairOfLowerKappa`、`MissingLowerKappaS00S01/S01S11`、`MissingLowerKappas`、`kappaPairActual_status` | 用真实 upper action + **missing lower kappa donor** 构造 pair datum；donor 未构造 | ❌ false | **conditional**；`Missing*` 精确记录 |
| `LinkedKappaActual.lean` | `linkedCommonGroup`, `linkedKappaLower`, `linkedKappaData`, `MissingLinkedKappaData`, `linkedKappaActual_status` | 由 strip link 构造 linked common group/lower kappa；记录 missing 数据 | ❌ false | **conditional**；`MissingLinkedKappaData` |
| `LowerKappaDonorActual.lean` | `linkS00S01`, `linkS01S11`, `LowerKappaDonorS00S01/S01S11`, `pairS00S01OfDonor`, `MissingLinkedKappaData`, `MissingLinkedKappaPackage`, `lowerKappaDonorActual_status` | 真实 strip links + conditional donor；donor 未构造 | ❌ false | **conditional**；`MissingLinkedKappaPackage` |
| `Mzk1KappaLemmaActual.lean` | `sL`, `AL`, `SSIneqKappa`, `kappa_factor`, `kappa_bound`, `ssIneqKappa_one` | 纯实数模型：`SSIneqKappa (l logq κ V) := (sL l - κ)*AL l logq ≤ V`；kappa 交叉项代数 | ✅ true | 无 Missing；**model-level，不是 κ-coric** |
| `S1388KappaSourceUnitsActual.lean` | `middleKappaUpper/Lower`, `actualMiddlePairDatum`, `..._kappaUpper_eq_link` 等 | 真实 source units（S01）+ 非 refl Kummer 代表；doc L30–40 明说 paper 的 `O^x(G)` module/action 与 identification 缺失 | ✅ true | **conditional**：paper `O^x(G)` 未构造；文件自带 `#print axioms` 探针 |
| `S1399KappaOxGActual.lean` | `S1399PaperOxGModule`（first field: paper O^x(G) module/action），`S1399ActualPairDatum`, `..._kappaUpper_link` 等 | 记录 paper O^x(G) 第一字段与 pair datum 的链接；first field 无一般 inhabitant | ✅ true | **conditional**：O^x(G) algorithm 未构造 |
| `S1425KappaOxGActual.lean` | `S1425PaperOxGModuleActual`, `..._sourceUnits`, `..._sourceAction`, `..._groupEquiv`, `..._unitsEquiv` | 给 S1399 first field 一个**真实** inhabitant（第二 lattice 点的 F-prime-strip units + link） | ✅ true | **conditional**：paper 的 `G ↦ O^x(G)` 算法与 `Aut(‡A)=G_w` 识别未构造（doc L19–24） |
| `S1959PaperCoricVerticesActual.lean` | `tmVertex`, `env/gau/LGP/lgp`, `upperEvaluation`, `lowerHorizontal`, `leftKummer`, `rightKummer`, `..._strip` | 四个 **source strips** 的 reduced Kummer/evaluation 方块；doc L37–86 明确：**没有 paper 的四个 coric vertices、没有 F^⊩ carrier、没有 theta/Gaussian monoid、没有 `κ^×μ` 从 source data 构造** | ✅ true | **conditional / 大幅 missing**（`PsiFenv` 等为 first missing） |
| `S2974VerticalCoricityGateActual.lean` | `S2974VerticalCoricityGate`, `S2974DThetaRealizationGate`, `S2974_bridge` | vertical coricity gate；非 κ-coric 函数 | ✅ true | 无（但非本问题） |
| `S2975A6QIsPrestackActual.lean` | `S2975A6QIsPrestack`, `S2975A6QIsPrestack_false` | A6Q prestack 反例；非 κ-coric | ✅ true | 无 |
| `S2975ThetaLinkCoricityConnection.lean` | `S2975CoricityThetaLink`, `S2975Connection`, `S2975_to_CThetaPaper_lowerBound` | theta-link coricity 连接；非 κ-coric 函数 | ✅ true | 无 |

## 2. 关键判定：没有任何对象给出 κ-coric 函数赋值/范数

逐条检查「是否能给出 `κ-coric 函数在各位的赋值/范数`」：

| 候选对象 | 为什么不行 |
|---|---|
| `KappaOrbitUnitsActionDatum.sourceUnits` | 字段类型 `V → Type` + `CommGroup`，`sourceAction : G →* MulAut`；**没有 `→ ℝ` 的赋值/范数，没有 `ord_v`，不是线丛** |
| `TimesMuKummer.Isomorphism` / `TimesMuQuotient` | 只是 monoid/action 的同构，作用在 torsion quotient 上；无数值不变量 |
| `coricModule`（`ℂ`,`D.M`,`D.K` 等） | 任意载体 Type；`coricKummerLink` 为 Prop；没有逐位赋值/arch 范数 |
| `S1388/S1399/S1425` 的 `O^x(G)` first field | 只有 `sourceUnits : V → Type` + action；doc 明说 group-theoretic algorithm 未构造；没有赋值 |
| `S1959` 的 coric vertices | 只是 source strips 的 reduced square；doc 明说没有 paper coric vertices / F^⊩ / κ^×μ；无赋值 |
| `Mzk1KappaLemmaActual` 的 `κ` | 纯实数模型中的标量；不是函数，也不是逐位赋值 |

**结论：没有可用对象。** face5 的 `Face5SectionData`（需要 `degNorm`/`archTerm`/`section_nonzero`/`deg_identity`）**不能**从现有 κ/coric 数据填充。

## 3. 对照 IUT I Example 5.1(v)：要补什么

IUT I Example 5.1(v) 的内容（根 `Iut/LogLink/Thm311Rest.lean:108` 也明确列为**未形式化**）：
1. **κ-coric functions**：在 κ-coric 数据上定义的整体函数（带 `F_mod`/`π₁^{κ-sol}` 作用与 cyclotomic rigidity）；
2. **`π₁^{κ-sol}(D^⊛)`**：κ-solvable 基本群；
3. **cyclotomic rigidity**（IUT I Ex 5.1(v) 版本；注意 `EtaleTheta/Env/CycRigidity.lean` 是 [EtTh] mono-theta 环境版本，**不是** IUT I 版本）。

要对 face5 可用，还需额外的**算术字典**：
- 每个位 `v` 的局部赋值/范数（`ord_v`, arch `|·|_v`）和这些函数到 **Arakelov 线丛**（`ArithLineBundle.fin/inf`, `degNorm`，`Iut/Arakelov/LineBundle.lean:69–105`）的映射；
- 截面非零/整性（`x ≠ 0` 且 `−Σ_w log‖x‖_w ≥ 0`）与 arch 界。

## 4. 最短补法（诚实路线）

**不能**用现有对象冒充。最短路径：

### 方案 A（推荐用于 face5 的**条件接口**）
定义一个显式的**外部/class-B 接口** `KappaCoricInterface`（不是定理，登记为假设）：
```lean
structure KappaCoricInterface (D : InitialThetaData) where
  -- IUT I Ex 5.1(v) 缺失层的字段（assumed）
  kappaCoricFun : (D.Fmod) → Type          -- κ-coric 函数载体（真实定义待补）
  pi1Ksol : Type                            -- π₁^{κ-sol}(D^⊛)
  cyclotomicRigidity : Prop                -- IUT I Ex 5.1(v) 的 cyclotomic rigidity
  -- 算术字典（必须同时假设，不能由现有数据导出）
  localAbs : (v : FinitePlace D.Kt) → kappaCoricFun → ℝ
  archAbs  : (v : InfinitePlace D.Kt) → kappaCoricFun → ℝ
  norm_dictionary : Prop                   -- 与 ArithLineBundle.fin/inf、degNorm 的对应
  section_nonzero : Prop
  arch_bound : Prop
```
然后 face5 的 `Face5SectionData` 只在该接口的非空实例下可陈述；**不能证明 `Nonempty`**，也不能 gate-green 声称。

### 方案 B（真正补 IUT I Ex 5.1(v)，大工程）
1. 定义 κ-coric functions（IUT I Example 5.1(v) 的 global realified Frobenioid 上的函数）；
2. 定义 `π₁^{κ-sol}(D^⊛)` 与 cyclotomic rigidity（独立于 [EtTh] 的 mono-theta 版本）；
3. 证明逐位赋值/arch 范数字典（到 `ArithLineBundle`）；
4. 才能谈 face5 截面。**这是 Layer B 级缺口，不是当前 face5 可以现成调用的对象。**

### 方案 C（若只想要一个**模型级**检查，不碰 IUT I）
在 `Face5SectionData` 中显式保留 `section_nonzero : Prop` 与 `arch_bound : Prop` 作为**假设字段**，把 κ-coric 来源写成 `KappaCoricInterface` 的字段；只做条件定理/数据；不要声称由 lana 提供。

## 5. 附：olean/gate 状态说明（含 A914 探针实测）

**A914 gate 探针**（`tmp/kappa_gate_probe.lean`，编译 EXIT 非零仅因 S1959 名字未找到；其余全部通过）：
- `S1388.actualMiddlePairDatum`、`S1399.S1399ActualPairDatum_kappaUpper_link`、`S1425.S1425PaperOxGModuleActual_sourceUnits`、`S2974.S2974_bridge`、`S2975.S2975_to_CThetaPaper_lowerBound`、`Mzk1KappaLemmaActual.kappa_factor`、`KappaOrbitUnitsActionDatum.kappa_equivariant` ⇒ 均只依赖 `[propext, Classical.choice, Quot.sound]`（green）；
- `S1959PaperCoricVerticesActual.upperEvaluation_strip` 在探针中 unknownIdentifier（可能 namespace/olean 版本名不同；不影响“无 κ-coric 赋值”的结论）。

- 表中 olean=true 表示 `.lake/build/lib/lean/<module>.olean` 存在；**本审计未对全部模块重跑 `#print axioms`**（除 `S1388` 源内自带 `#print axioms` 探针）。源级扫描未发现实际 `sorry`/`axiom`（`KappaOrbitPairActual` 等 docstring 里的 “sorry” 只是文字）；
- `KappaOrbitPairActual`/`LinkedKappaActual`/`LowerKappaDonorActual` olean=false（未编/conditional），不能作 green 证据；
- `KappaOrbit` 接口的 `Obligation`/frozen interface 是**接口条件**，不是已构造的算术对象；`canonicalDatumOfFactorization` 用 identity 完成，`sourceUnits` 不是 paper 的 `O^x(G)`。

## 6. 一句话回报

**能做：记录 κ/coric 的**同构/轨道/接口**（KappaOrbit、S1388/S1399/S1425 的 units/pair datum、S1959 的 reduced coric vertices）。**
**不能做：从现有定义读出 κ-coric 函数的逐位赋值/范数**——没有任何对象有 `ord_v`/arch norm/线丛截面；face5 S3 不可用。
**最短补法：显式 `KappaCoricInterface` 假设（class-B）+ 算术字典假设**；真正补 IUT I Ex 5.1(v) 是 Layer B 大工程。