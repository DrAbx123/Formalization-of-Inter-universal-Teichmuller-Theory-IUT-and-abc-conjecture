# face5 截面构造：完整路线图与详细规划

> 版本：A914（2026-11-12）  
> 状态：规划文件（PLAN ONLY）；不代表任何未证结论  
> 目标读者：后续接手 agent / 人类审阅者  
> 纪律：所有 lana 行号以仓库根 `Iut/` 树为准；`tmp/sheaf/lana*` 旧副本作废；引用必须标树根。

## 0. 摘要

face5 是当前唯一未被判无效的攻击面：把 SSIneq / paper variant 的数值不等式
换成 Arakelov 线丛上的截面存在性问题，再试图显式构造截面。
本文件给出：

- 目标的精确定义与验收标准；
- 已核实的对象、公式与现有 Lean/green 资产索引；
- 构造路线 S0–S5，每阶段的输入、步骤、产出、gate、失败判据、工作量与 owner；
- 候选截面的穷尽清单与各自的计算公式、预期成败；
- 判定门 D1–D5（何时继续、何时否决、何时转入替代路线）；
- 替代路线（受限类定理、纯数值不等式）与最终交付形态；
- 附：精确公式汇总、文件清单、验收命令。

任何阶段不得以「换说法」「引入未登记假设」「假定结论」通过；所有中间命题必须可编译并过 `#print axioms` trio 检查。

---

## 1. 目标与验收

### 1.1 最终要证的命题（paper 归一化形式）

记 `nC = (l-1)/2`、`sF = sFactor nC = (nC+1)(2nC+1)/6 = l(l+1)/12`、`A = |log q|/(2*l)`，其中 `q` 为 q-pilot。
逐位（有限位 v）：

```
T_v := (sF - 1) * weight_v * ord_v(q_v) * log p_v / (2*l)     -- q 侧，固有（无分配自由）
H_v := (1/nC) * sum_i hullPacket_i(v)                          -- hull 侧（lana VcI:689/741）
H_inf := (1/nC) * sum_i hullPacket_i(inf)                      -- arch 侧
```

face5 的数值目标：

```
Goal (numeric):   forall D : InitialThetaData,  sum_{v finite} T_v(D) <= sum_{v finite} H_v(D) + H_inf(D)
Goal (paper):     (sF - 1) * A <= V = (1/nC) * sum_i sum_v hullPacket_i(v)
```

两者等价（`VcI.lean:741 logVol_hull_vcI_eq` + `T_v/H_v` 分解）。

### 1.2 截面的存在性形式

差丛（逐 capsule 与聚合两版）：

```
H_j := det(hull_j) (x) L_q^{ -(j^2 - 1)/(2*l) }        -- 逐 capsule
H   := det(hull)   (x) L_q^{ -(sF - 1) }               -- 聚合（sF 见上）
```

若存在非零整体截面 `x` of `H`，且其逐位范数（`-log ||x||_v`）满足 finite 位非负、arch 位不超过预算，
则 `degNorm H >= 0`，即 `V - (sF-1)A >= 0`，即 Goal。

这就是 `Face5SectionData` 的义务。骨架定理已在 `Mzk1Face5ProofActual`（green, trio）：

```
structure Face5SectionData where
  H : ...            -- 差丛数据
  x : ...            -- 非零截面
  section_ne_zero : x != 0
  finNorm : RationalPlace -> Real      -- 逐位有限范数
  archNorm : Real
  degNorm_eq : degNorm H = sum_v finNorm v + archNorm
  productFormula_accounting : ...
theorem face5_inequality_of_section (S : Face5SectionData) : (sF-1)*A <= V
theorem face5_inequality_from_perplace (...) : ...
```

### 1.3 验收标准（每阶段通用）

1. 单文件 `lake env lean` EXIT=0；olean 生成；
2. 目标声明 `#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`；
3. 不得出现 `sorry`/`admit`/新增 `axiom`/`PUnit`/`True` 占位/未登记的假设；
4. 每个新假设必须作为显式结构字段，并在文件头登记；
5. 数值/模型计算必须与 Lean 定理分开标注（模型 ≠ 定理）。

---

## 2. 已核实的对象与公式（不得再重复推导）

### 2.1 V 的定义与 q-无关性

- `Iut/Wall/Ind3.lean:58-62`：
  - `vcIComp i .finite p c = LocalTheory.shell …`
  - `vcIComp i .infinite c = LocalTheory.logShell …`
  - **不含** `qroot`/`scaleElt`/q^{j^2}；
- `Iut/WallEquiv/VcI.lean`：
  - `:689 hullPacket`；`:741 logVol_hull_vcI_eq`：`V = (1/nC) sum_i sum_v hullPacket_i(v)`；
  - `:806 hullPacket_finite = sum_c w_c sum_j logShellRadius(...) * log p`；
  - `:844 hullPacket_tame = sum_c w_c sum_j (1 - 1/e_cj) * log p`；
  - `:725 hullPacket - vcIPacket = defectPacket`；`:762 logVol_hull_vcI_sub_eq`；
  - `:630 shellExcess`、`:93 orderVol`、`:631 ShellExcessAdditive`（named, 未证）、`:640 PacketIndexFormulaGalois`（named, 未证）；
- **V 对 q 幅度无关**（qOrder 只经 `absLogQ` 进入 LHS）；
- 因此 SSIneq 的冻结 RHS 形式对足够大 q 为假（模型内），paper 的 variant 含 `gap` 项：
  `rhs = V - sF*A + gap`、`gap >= 0`（`WallEquiv/Gap.lean:505/514`），variant `<=> (sF-1)A <= V + gap`。

### 2.2 tame 位为 0 是真实的

- `Iut/Concrete/LocalConstruct/LocalLogShell.lean:39-41`：`logShell = { y | exists u, ||u-1||<1 and y=(2p)^{-1} padicLog u }`；
- 同文件 `:101-107 logShell_eq_integer`：奇 p 非分歧时 `logShell = 整数环`；
- 所以 tame `hullPacket = 0`，`(2p)^{-1}` 已计入，**不应再加 -log(2p)**；
- 于是 tame 位 `H_v - T_v = -T_v < 0`；**all-tame 情形 Goal 不可能成立** ⇒ 必须依赖 wild（e>=2，`1-1/e>0`）或 arch。

### 2.3 arch 项

- 常数 `archConstant = log(sqrt 2 * pi) = log 2/2 + log pi ≈ 1.491303`（`Mzk1DifferentDictionaryActual.archConstant_eq_log`；`Mzk1Chain2VolumeDataActual.archTerm_eq_log`）；
- `archLogShell` compact、正测度、`archLogShell subset (sqrt(2pi))^|I| * archIntegral`（`Iut/Concrete/LocalConstruct/ArchLogShell.lean`）；
- 数值样例中 arch 主导：去掉 arch 后余量仅 +0.2295（A912 wild numerics 文档）。

### 2.4 已经失败/无效的候选（不得重复）

| 候选 | 结论 | 依据 |
|---|---|---|
| Gaussian avgDeg（`Gauss.lean:228`） | 等价改写（需 `hullLogVol >= sF*A`，若成立 SSIneq 立即成立） | `Mzk1SSIneqFromGaussActual`；`FACE5-FINAL.md` |
| `disc(Psi_l)` | 主除子、总度 0、整体恒等式 | `Mzk1Face5DiscInterfaceActual`；`FACE5-SECTION-DISC.md` |
| κ-coric（lana 根树） | 根树未形式化（`Thm311Rest:108` 自注 (d) 项） | `FACE5-SECTION-CORIC.md` |
| 有理函数扩展（实数模型） | 平凡（一个主除子约束可吸收任意逐位目标） | `FACE5-SECTION-SEARCH2.md` |
| 有理函数扩展（整数 ord） | 无精确解（残差 ±0.0281） | 同上 |

### 2.5 我们仓库的 κ/coric 资产（reduced 层）

- `LeanFormal/IUT/IUTII/Frobenioid/SourceKappaOrbitFactorizationProvider.lean`、`SourceKappaOrbitUnitsActionSupply.lean`：κ-orbit units action/pair factorization 供给；
- `KappaOrbitPairActual`、`LinkedKappaActual`、`LowerKappaDonorActual`：conditional / 缺 lower κ（文件头自注）；
- `S1388KappaSourceUnitsActual`、`S1399KappaOxGActual`、`S1425KappaOxGActual`：`O^x(G)` module/action vs 实际 middle-strip units（部分字段、无 inhabitant）；
- `S1959PaperCoricVerticesActual`：paper 四 coric 顶点的 times-mu **reduced 模型**（自注不是 paper 的 F^⊩ 顶点）；
- `S2974VerticalCoricityGateActual`、`S2975ThetaLinkCoricityConnection`：vertical coricity gate、q-pilot coricity；
- `LeanFormal/IUT/IUTII/Kummer/*`：`coricModule`、`coricKummerLink`、coric log-shell 载体、archimedean log-Kummer 校准；
- **没有** IUT I Example 5.1(v) 的 κ-coric functions / `pi_1^{κ-sol}` / cyclotomic rigidity 本体。

### 2.6 Arakelov 次数工具（lana 参考）

- `Iut/Arakelov/LineBundle.lean:84-105`：`finDeg = -log ||fin w||`、`infDeg = -mult*log inf`、`deg = sum finDeg + sum infDeg`、`degNorm = deg/[K:Q]`；`principal`、`deg_mul_principal`；
- `Container.lean:140/145/196`：`sectDegAt/sectDeg/degNorm_toBundle`（字典恒等式）；
- `ArchScaling.lean:205/210/235/496/503`：`archSectDeg/fullSectDeg/degNorm_toBundle/logVol_fullScale_integral_eq_degNorm/logVol_fullScaleConst_eq_neg_degNorm`；
- `QPilot.lean:63/78/109/150/157/172/196/210/215/218/221/226/230/241/252/262`：`qDivisor`、`degNorm_qDivisor`、`lhs_eq_neg_degNorm_qDivisor`、`qPowDatum`、`qPow`、`isModInvariant_qPowDatum`、`sectDeg_qPowDatum`、`degNorm_qPowDatum`、`qPilotBundle`、`thetaBundle j = qPowDatum (j^2)`、`degNorm_qPilotBundle`、`degNorm_qPilotBundle_eq`、`degNorm_thetaBundle j = j^2 * absLogQ`、`logVol_qRegion_eq_neg_degNorm`、`logVol_pow_integral_eq_degNorm`、`logVol_lgp_integral_eq_degNorm`；

---

## 3. 构造路线图（S0–S5）

### S0（1 周，确定可完成）：数据层形式化

**目标**：把差丛、局部度、截面数据全部写成 Lean 结构与恒等式，使后续所有候选都在同一接口下检验。

步骤：

1. `Face5BundleData D`：
   - `degH := V - (sF-1)*A`；
   - `degH_fin v := H_v - T_v`（用 2.1 的 `H_v` 与 1.1 的 `T_v`）；
   - `degH_arch := H_inf`；
   - 定理 `degH_eq_sum : degH = sum_v degH_fin v + degH_arch`（place 分解，接口/算术）；
2. `Face5SectionData`（与 `Mzk1Face5ProofActual` 对接）：
   - 字段：`H`、`x`、`section_ne_zero`、`finNorm : RationalPlace -> Real`、`archNorm`、`degNorm_eq`、`productFormula_accounting`、`archBudget`；
   - 定理：`face5_inequality_of_section`（已 green，勿重写）；
3. 数值/符号检查接口：`evalFinNorm`、`evalArchNorm`、`checkGoal`（返回 Bool/Prop），用于候选筛选。

**产出**：`Mzk1Face5BundleActual.lean`（olean + trio）。

**失败判据**：若 `degH_eq` 无法在定义层闭合（例如 V 的分解与 T_v 索引不一致），先修索引（`RationalPlace` 对齐），不得引入假设。

### S1（1–2 周，确定可完成）：候选截面的逐位范数计算

**目标**：对每个候选给出**独立于不等式**的逐位范数公式（有限位 + arch），并数值/符号化。

候选与需要的对象：

#### C1. 加权 theta 乘积 `x = prod_j theta_j^{a_j}`
- 需要的对象：theta 值 `theta_j` 作为**代数数/局部域元素**（每个 capsule j、每个位 v）；
  - lana：`EtaleTheta.lgpValue`、`Gauss.lean` 的 `gaussGen v j = lgpValue D v (j+1)`（源级）；
  - 我们：`S3137QThetaPilotLogVolumeReadingsActual` 等 theta 值读数（green）；
- 逐位有限范数：`-log ||theta_j||_v = j^2 * ord_v(q) * log p_v / (2*l)`（高斯生成元的赋值；需与 2.1 的 `T_v` 同索引）；
- arch 范数：由 Gaussian 范数给出；`Gauss.lean avgDeg_gaussian` 给出 `avgDeg(q^{j^2}) = sF * (-log||q||)`，即 arch 侧加权和；
- 自由度：`a_j in Z`（或 `Z/nC`）；已有结果：2 权（j=1,2）对 l=5、q=22 无精确解（秩不足，见 FACE5-WEIGHT-SEARCH）；
- 下一步：穷尽更多权向量（含 `a_j` 取负、按 capsule 不同 support），或允许不同 j 的 theta 值来自不同 capsule；
- 预期：有限位范数是 `j^2*ord_v(q)*log p_v/(2*l)` 的整数线性组合，与 `T_v` 结构相同 ⇒ 很可能只能得恒等式或需要额外自由度；

#### C2. q 的幂（值群）
- 范数：`-log ||q^a||_v = a * ord_v(q) * log p_v`；arch 无（q 为 p-adic 值群元素）；
- 预期：值群进 unit 部分会破坏 log-shell 兼容（`Iut/ThetaLink/Wall.lean:145/294/299 not_logShellCompat_*`），**否决概率高**；

#### C3. l-分点值 / 判别式
- 需要的对象：division polynomial `Psi_l`、其根/判别式的代数数表示（vendor `EllipticCurves`/`Iut/Torsion/EDS` 有基础设施，但 Basic 未编）；
- 范数：`v_p(disc) = a v_p(l) + b v_p(Delta)` 型（指数待核）；
- 已判：判别式是**有理数** ⇒ 主除子 ⇒ 总度 0 ⇒ 不能给正下界（FACE5-SECTION-DISC）；
- 残余可能：取**单个 l-分点值**（不是判别式）——其除子不是主除子的平凡情形；需算其逐位赋值与 arch 范数；

#### C4. reduced coric 顶点上的单位
- 需要的对象：`S1959` 的 coric 顶点载体 / `IUTII/Kummer` 的 `coricModule`/`coricKummerLink`；
- 范数：unit 的赋值由 `coricKummerLink`/log-shell 半径给出（模型层可算）；
- 风险：这些是 reduced 模型，不保证与 paper 对象一致；需要先做对象识别（见 S4）；

#### C5. κ-coric functions（IUT I Example 5.1(v)）
- 需要的对象：`D^⊛` 上的 κ-coric 函数、`pi_1^{κ-sol}`、cyclotomic rigidity；**仓库未形式化**（我们与 lana 都只有 reduced/κ-orbit 层）；
- 若补：先定义 κ-coric 函数（作为 `D^⊛` 上的函数/线丛截面），再算其逐位赋值与 arch 范数；
- 这是 Layer B（月级）工程；见 S4；

#### C6. 有理函数修正 `x = c * prod theta^{a} * r`
- `r in K^x`：`ord_v(r)` 任意整值，受**主除子约束** `sum_v [k_v:Q] ord_v(r) = 0`（一个线性方程）；
- 实数模型：可吸收任意逐位目标（平凡）；整数模型：2 权下残差 ±0.0281（FACE5-SECTION-SEARCH2）；
- 进一步：允许 `r` 取**主除子类群生成元**（若 `K` 的类群可由显式元素生成）——需要 number field/class group 形式化（我们目前无）；

#### C7. 合成候选
- `x = (prod_j theta_j^{a_j}) * (unit from coric vertex) * r`；
- 逐位范数 = 各因子范数之和；自由度 = `a_j` + unit 指数 + `r` 的除子；
- 需要 C1/C4/C6 的数值先落地；

**产出**：`coord/FACE5-CANDIDATES.md`（每候选：公式、所需对象、已算数值、成败）；`Mzk1Face5CandidateDataActual.lean`（能 Lean 化的逐位范数公式）。

**失败判据**：若所有候选的逐位范数都是 `T_v` 的恒等组合（即 `sum finNorm = k * sum T_v`），则候选族只能给恒等式 ⇒ 转 S4；
若某候选的 `sum finNorm` 与 `V - (sF-1)A` 差一个显式非负项，进入 S2。

### S2（2–4 周，中风险）：全局化与 arch 估计

**目标**：把候选变成真正的**有理截面**，验证 product formula 与 arch 范数界。

步骤：

1. 选定候选 `x`（S1 的输出），写出其除子 `div(x) = sum_v n_v [v]`；
2. 验证 `degNorm H = sum_v (-log ||x||_v)`（按度量规范化后）；这是 `degNorm_eq` 字段的实例化；
3. 计算 arch 范数：需要 `x` 在 arch 位的取值（theta 值的 Gaussian 范数/复数绝对值）；
4. 检查 integrality（finite 位 `-log ||x||_v >= 0`）——**注意**：由于 tame 位 `degH_fin < 0`，若要求每 finite 位非负则该位不可能；
   因此必须允许有限位有界负值，只要 `sum_fin (-log||x||_v) >= -archBudget`；
5. 若 arch 范数估计需要 Mathlib 的 `pi`/`log` 界（archConstant 的数值界），用 `norm_num`/`Real.pi_gt_*` 等证明；
6. 产出：`Mzk1Face5SectionDataActual.lean`（构造 Face5SectionData 的实例）+ gate；

**失败判据**：若 `x` 的 arch 范数无法控制（或需要独立于不等式的输入），退回 S1 换候选或 S4。

### S3（2–4 周，中高风险）：类群/effectivity 补洞

**目标**：当候选的除子不是主除子时，用类群/Minkowski 理论判断能否修正为截面。

步骤：

1. 形式化 `K` 的整数环理想类群（我们目前没有 number field 类群基础设施；需引入/移植）；
2. 差丛 `H` 的除子类 `[div]` 与主除子之比 `[div] in Cl(K)`；
3. 若 `[div]` 非平凡：用 Minkowski/ideal estimates 找等效除子 `div + (f)` 使 `f` 的范数可控；
4. 若类群过大/无法控制 ⇒ 该候选不可行；

**产出**：`coord/FACE5-CLASSGROUP.md` + 可 Lean 化的条件定理；

**失败判据**：类群不可控 ⇒ 放弃该候选，转 S4。

### S4（月级，高风险）：补 κ-coric / anabelian 层

**目标**：形式化 IUT I Example 5.1(v) 的 κ-coric functions / `pi_1^{κ-sol}` / cyclotomic rigidity，并用其作为截面来源。

为何需要：C5 是目前唯一可能给出**非平凡逐位赋值**的候选族；reduced coric 顶点不含函数值。

步骤：

1. 审计我们现有 reduced 层（`S1959`/`S2974/2975`/`IUTII Kummer coric*`）与 IUT I Ex 5.1(v) 的差距；
2. 定义 `KappaCoricFunction`（`D^⊛` 上的函数）与 `pi_1^{κ-sol}` 的结构；
3. 证明 κ-coric 函数的**逐位赋值公式**（这是截面需要的唯一硬输入）；
4. 证明 cyclotomic rigidity（可能需要 Mathlib 分圆域/单位根工具）；
5. 用其构造 `Face5SectionData`；

**失败判据**：若 κ-coric 函数的赋值无法给出可控下界（或需要新的未形式化定理），记录并停止。

**预估**：3–6 个月（取决于 reduced 层能复用多少）；建议作为长期项，不阻塞 S1–S3/S4'。

### S4'（并行，低风险）：直接攻纯数值不等式的受限类

**目标**：不造截面，直接对受限类证明 `sum T_v <= sum H_v + H_inf`。

受限类：

1. **素导子**：已有 `Mzk1PrimeConductorRouteActual`（Mestre-Oesterle 外部输入 + T(l) 算术余量），补 `D_exact` 下界即可成类定理；
2. **omega(N) <= 2**：P2018 Thm1.5 的相对 delta 比较 + 局部计算；
3. **固定有限坏位集（wild 主导）**：对固定 S 外的半稳定曲线，用 arch/wild 缓冲给出一致界；
4. **数值探索**：对大量 D 计算余量 `sum H + H_inf - sum T`，找最小余量与失败模式（若找到反例 ⇒ face5 的数值形式在某个 D 失败，需修正目标/归一化）。

**产出**：每类一个条件/无条件定理（外部输入显式登记）；`coord/RESTRICTED-CLASS-RESULTS.md`；

**失败判据**：若数值探索找到反例 ⇒ 检查目标形式（variant vs SSIneq）并回报；不得掩盖。

### S5（1 周，收尾）：交付与审计

1. `coord/FACE5-FINAL.md` 更新：S0–S4' 全部结果；
2. 全链 gate：`Mzk1Face5ProofActual`、`Mzk1Face5BundleActual`、候选数据文件、受限类定理；
3. 若未完成构造：明确记录「差丛/局部度/候选穷尽/失败判据」，并把唯一开放项写成 `Face5ConstructionObligation`（显式结构字段）；
4. 若完成构造：给出 `Face5SectionData` 实例与 `face5_inequality` 的完整证明，并接 `paperGap -> Cor312Conclusion` 链；

---

## 4. 判定门（Decision Gates）

| 门 | 触发 | 通过条件 | 失败动作 |
|---|---|---|---|
| D1 | S0 完成 | `degH_eq_sum` 编译；索引对齐 | 修索引；不引入假设 |
| D2 | S1 完成 | 至少一个候选的 `sum finNorm` 与 `degH` 差显式非负项 | 全恒等 ⇒ 转 S4'（数值不等式）；或转 S4（κ-coric） |
| D3 | S2 完成 | `Face5SectionData` 实例编译 + trio | 候选失败 ⇒ 换候选/转 S4 |
| D4 | S4' 受限类 | 至少一个类定理 unconditional（外部输入显式） | 记录并继续其他类 |
| D5 | S4 κ-coric | 赋值公式 + 截面构造可编译 | 记录并停止（月级工程） |

---

## 5. 候选截面穷尽清单（用于 S1 执行）

| id | 截面 | 逐位有限范数 | arch | 需要对象 | 先验判断 |
|---|---|---|---|---|---|
| C1 | `prod_j theta_j^{a_j}` | `sum_j a_j * j^2 * ord_v(q) * log p_v/(2l)` | Gaussian 和 = `sF * sum_j a_j...` | theta 值代数表示（`EtaleTheta.lgpValue`） | 2 权已失败；需扩权 |
| C2 | `q^a` | `a * ord_v(q) * log p_v` | 0 | q 值群元素 | 高概率否决（log-shell 兼容） |
| C3 | `disc(Psi_l)` | 主除子，总度 0 | 0 | division polynomial | 已否决 |
| C3' | 单个 `Psi_l` 根 | `a v_p(l) + b v_p(Delta)`（待核） | 需复数绝对值 | division values | 待算 |
| C4 | coric vertex unit | `coricKummerLink` 给的赋值 | 模型层可算 | reduced coric 顶点 | 需对象识别 |
| C5 | κ-coric function | 需定义 IUT I Ex5.1(v) | 需定义 | 未形式化 | 长期项 |
| C6 | `c * prod theta * r` | 上述 + `ord_v(r)` | 由 `r` 的 arch | `K^x` + 类群 | 实数平凡，整数残差 0.0281 |
| C7 | 合成 | 各因子之和 | 各因子之和 | C1/C4/C6 | 待 C1/C4 数据 |

---

## 6. 精确公式汇总（执行时直接引用）

```
nC = (l-1)/2
sF = (nC+1)*(2*nC+1)/6 = l*(l+1)/12
A = |log q|/(2*l) = logQ/(2*l)，logQ = sum_w weight_w*ord_w(q_w)*log p_w
T_v = (sF-1)*weight_v*ord_v(q_v)*log p_v/(2*l)
H_v = (1/nC)*sum_i hullPacket_i(v)
hullPacket_finite = sum_c w_c * sum_j logShellRadius(...) * log p
hullPacket_tame = sum_c w_c * sum_j (1-1/e_cj)*log p
rho_cj = (1-1/e_cj) + delta_cj（wild）
H_inf = (1/nC)*sum_i archDefect_i，archConstant = log(sqrt 2 * pi) = 1.491303
V = (1/nC)*sum_i sum_v hullPacket_i(v)
Goal: sum_fin T_v <= sum_fin H_v + H_inf
差丛: H = det(hull) (x) L_q^{-(sF-1)}
```

数值参考（A912，l=5，q=22，坏位 {2,11}）：

```
p=2 wild: H=0.693147, T=0.103972
p=11 tame: H=0,        T=0.359684
arch:     H=1.491303,  T=0
sum:      H=2.184450,  T=0.463656,  margin=+1.720794
去掉 arch 后 margin=+0.229491（紧）
```

---

## 7. 文件与命令清单

### 已有 green / 参考文件

- `tmp/sheaf/xif/paper/Mzk1Face5ProofActual.lean`（骨架，trio）；
- `tmp/sheaf/xif/paper/Mzk1Face5DataActual.lean`（待 import 修复）；
- `tmp/sheaf/xif/paper/Mzk1Face5DiscInterfaceActual.lean`（disc 否决接口，trio）；
- `tmp/sheaf/xif/paper/Mzk1E1DictionaryActual.lean`（E1 接口，trio）；
- `tmp/sheaf/xif/paper/Mzk1OurFrameworkABCActual.lean`（条件装配，trio）；
- `coord/FACE5-FINAL.md`、`coord/FACE5-WILD-NUMERICS.md`、`coord/WILD-HULLPACKET.md`、`coord/FACE5-SECTION-SEARCH2.md`、`coord/FACE5-NORMALIZATION*.md`、`coord/FACE5-SECTION-*.md`；

### 产出目标

- `Mzk1Face5BundleActual.lean`（S0）；
- `Mzk1Face5CandidateDataActual.lean`（S1）；
- `Mzk1Face5SectionDataActual.lean`（S2，若成功）；
- `coord/FACE5-CANDIDATES.md`、`coord/FACE5-CLASSGROUP.md`、`coord/RESTRICTED-CLASS-RESULTS.md`、`coord/KAPPA-CORIC-AUDIT.md`；

### 验收命令（单文件）

```powershell
cd D:\lean
lake env lean tmp/sheaf/xif/paper/Mzk1Face5BundleActual.lean
# 期望 EXIT=0 + olean
# 然后 #print axioms 检查（用 tmp 下的 probe 文件）
```

---

## 8. 风险、非目标与停止条件

### 非目标（明确不做）

- 不用「换说法」的等价改写作为进展；
- 不假设 SSIneq/variant；
- 不修改 paper 对象定义以迁就证明；
- 不把模型数值当定理；
- 不引入未登记假设/额外 axiom/sorry；

### 风险

1. tame 位负目标 ⇒ 每有限位非负的截面**不存在**；必须允许有界负值；若论文的 variant 要求整性，则目标形式需重新核对（variant vs SSIneq 的 gap 项）；
2. 候选截面族可能全部给出恒等式（如 Gaussian/disc）；
3. κ-coric 补层是月级工程且不保证截面存在；
4. 类群/effectivity 需要 number field 基础设施（我们目前没有）；
5. 若 S1–S3 全失败且 S4 不可行：唯一结论是「face5 构造需要新数学/新层」，此时停止并保留 S4' 受限类结果；

### 停止条件

- D2 全恒等 + S4 判定不可行 ⇒ face5 构造封版为「需要 κ-coric 层」；
- S4' 找到反例 ⇒ 目标形式需修正，停止并回报；
- 所有工作必须保持 gate：无 sorry/axiom/trio 失败即注册问题；

---

## 9. 与其它链的接口

- `paperGap <-> Paper312Statement`（green，`Mzk1N3SharedContainerBridgeShaActual`）；
- `paperGap + qPilotReading<0 + IPL/SHE/APT evidence -> Cor312Conclusion`（green）；
- `Cor312Conclusion -> ClassicalABC`（lana `Iut.classicalABC_of_variant` 经 Tripod；我们缺字典时作为外部引用，需单独登记）；
- `ClassicalABCShape -> ABCConjecture`（green，`Mzk1ClassicalABCToOurABCActual`）；
- E1 字典（`Mzk1E1DictionaryActual`）、E4（待写）、E2 上箱（V3 OPEN）；

## 10. 总结

face5 的截面构造路线 = 数据层（S0）→ 候选范数（S1）→ 全局化（S2）→ 类群修正（S3）→ 或补 κ-coric 层（S4）/ 转受限类（S4'）。
前两阶段确定可完成；成功率最高的实质突破点在 S1 的 C1/C4/C7 候选与 S3 的类群控制；
S4 是月级备选；S4' 是不依赖截面的真实数学产出（素导子类等）。
任何阶段失败都必须以「明确记录 + 保持 gate」收尾，不得把失败包装成等价改写。

（本文件为路线图，不是结论；后续执行时逐项更新状态。）