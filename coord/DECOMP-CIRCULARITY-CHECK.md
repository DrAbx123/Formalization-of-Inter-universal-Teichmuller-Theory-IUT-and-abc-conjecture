# DECOMP-CIRCULARITY-CHECK — 分解候选循环性审查（A991）

日期：2026-11-12。**Status: READ-ONLY AUDIT；不编译、不新增 Lean。**
审查对象：`coord/DECOMP-PAIRING-CANDIDATES.md` 的 C1–C6（hull/abc/qpilot 产出的分解候选）；
相关目标/定义来源：`coord/C-MARGIN-FIX.md`、`coord/C0-EXACT-DERIVATION.md`、`coord/OUR-VOLUME-CHAIN.md`、
`Iut/Cor312/{LeftHandSide,RightHandSide}.lean`、`Iut/WallEquiv/{VcI,Gap}.lean`。

## 0. 目标口径与判定规则

先固定三个不同目标，禁止混用：

| 记号 | 定义 | 来源 |
|---|---|---|
| `M_ss`（SSIneq） | `V − (sF−1)·A` | `VcI.lean:889-891`（SSIneq ↔ `(sF−1)A ≤ V`） |
| `M_var`（framework variant） | `V + gap − (sF−1)·A` | `Gap.lean:523`；framework target |
| `M_paper`（paper margin） | `A − R`，其中 `R=−rhs` | `C-MARGIN-FIX.md` §2；`M = A-R` |

`DECOMP-PAIRING-CANDIDATES.md:3` 明确写 `M := V - (sF-1)*A`（SSIneq 归一化 wall），
不是 variant/paper。**任何 C1–C6 若未显式加 `gap` 或换成 `A−R`，不能声称证明 variant/Cor312。**

**判定规则**：
* **CIRCULAR**：候选不等式与目标（`M_ss≥0`/`M_var≥0`/`M_paper≥0`）在定义展开后等价（只需 `linarith`/`ring` 重排）；
* **INDEPENDENT-SUFFICIENT**：候选严格强于目标，且非负证明只用局部定义/已证引理（不 import 目标或目标等价物）；
* **PARTIAL**：候选只是目标的一部分，或需要额外条件（符号、buffer 在 M 中的归属）才能推出目标；
* **INVALID**：候选把不在 M 分解中的正项加进来，或公式本身符号/定义错误；
* **IDENTITY-ONLY**：只是已证恒等式，不提供新的非负性。

## 1. 审查清单（项 → 定义 → 非负证明依赖 → 判定）

| 项 | 定义（摘要） | 非负证明是否只用局部定义/已证引理？ | 与目标关系 | 判定 |
|---|---|---|---|---|
| C1 | `C1Bound v := T_v ≤ H_v`；`T_v=(sF−1)w_v ord_v(q_v)logp_v/(2l)`，`H_v=(1/nC)Σ hullPacket_i(v)` | 局部：`T_v/H_v` 定义 + `hullPacket_finite`；**但 H_v 在 ramified 处可为负**，C1 非普遍真；当前无证明 | `∀v C1 ⇒ Σ(H−T)≥0`；M_ss 还含 `arch−torsion`，**as stated 不足** | **PARTIAL**（非循环，但不足；需补 torsion/arch 条件） |
| C2 | `C2Bound p := Σ_{v|p}T_v ≤ Σ_{v|p}H_v + (1−1/e_p)logp` | 局部：`hullPacket_tame` 是已证公式；**但 M 分解没有独立 buffer 项**——若 H_v 取 tame 公式（C2 的意图），buffer 已在 H 内；若 H_v 取 finite/wild，buffer 是否属于 M 未证 | 只推出 `Σ(H−T)+buffer≥0`，不是 `M_ss≥0`；buffer 不在 M 中 | **INVALID/PARTIAL**（加项不在目标；需删 buffer 或给出其属于 M 的恒等式） |
| C3 | `C3Pair := (sF−1)A ≤ c_lana A + Σ(H−T)`，`c_lana=(sF−1)/(2l)` | `c_lana` 恒等式（`thetaSumPaper_eq_clana_mul`）已证；剩余正性仍回到 C1/C2 | 不等价目标；`C3Pair` 比 `Σ(H−T)≥0` **更强**（多要求 `(sF−1)A(1−1/(2l))`），但仅 identity-level；draft `(sF−1)A≤c_lana A` 对 A>0/l>1 **false** | **IDENTITY-ONLY / INVALID as written**；修正版无新算术 |
| C4 | `C4Bound deficit := deficit ≤ arch`；doc 写 `M = deficit + arch − torsion` | `deficit` 若取 `paperNormDeficit = LHS−RHS`，则 C4 是目标重排；**非负证明没有独立内容** | 目标 `M≥0` ⟺ `deficit ≤ arch−torsion`；torsion=0 时 C4 **恰好等价**目标；torsion>0 时 C4 太弱（只给 `deficit≤arch`） | **CIRCULAR（torsion=0）**；torsion>0 **INVALID/insufficient** |
| C5 | `C5Bound p e := T_p ≤ H_p + (1/e)logp` | 额外 `(1/e)logp` 是否已在 `H_p`（wild hull）中未核对；若已在则重复，若不在则不在 M 分解中 | 同 C2：只给带额外正项的不等式，不直接给 M_ss；不**等价**目标，但也不独立充分 | **PARTIAL/INVALID**（buffer 归属未定；不能当 M 的非负来源） |
| C6 | `C6Bound S := Σ_{v∈S}T_v ≤ Σ_{v∈S}H_v + arch − torsion`；theorem `C6Bound univ → 0≤M` | 若 `S=univ`，直接展开 M 定义；G1/G3 模型引理只在 proper S / 结构性控制时用 | `C6Bound univ` 与 `M_ss≥0` **定义展开后等价**（仅 `linarith`） | **CIRCULAR（univ）**；proper S 的 G 约束版另审（model-level） |

## 2. 逐项理由

### C1（per-place）
* `C1` 的 `T_v` 是 q-side 的局部项（A911 定义），`H_v` 是 finite theta-hull packet；两者都是局部定义，
  **不是**直接由 `M≥0` 或 `SSIneq` 定义。单看依赖图，它满足“只用局部定义”的**形式**；
* 但 `M_ss = Σ(H−T)+arch−torsion`（按 DECOMP 文档的分解）；C1 只给 `Σ(H−T)≥0`，
  要得 `M_ss≥0` 还需 `torsion≤arch` 或把 torsion 纳入 C1；当前 draft 未做；
* 此外 `H_v` 在 ramified places 可为负（`DECOMP` §C1 自己承认），`C1Bound` 并非全称可满足；
  **判定 PARTIAL**：不是 CIRCULAR，但作为“M≥0 的充分条件”不完整；若有人把它当“已证非负”应拒绝。

### C2（bad-prime group + tame buffer）
* `hullPacket_tame = Σ_c w_c Σ_j (1−1/e_j)logp`（`WILD-HULLPACKET` / `VcI.lean:844`）是 tame 值的**公式**；若 `H_v` 取 tame 值，则 buffer 已在 `H_v` 内；若 `H_v` 取 finite/wild 值，则 C2 的 buffer 是否对应 M 的某项**未证明**；
* `C2Bound` 在 RHS 再加 `(1−1/e_p)logp`，这**不是 M 分解中的独立项**；若 `H_v` 已取 tame，
  则 C2 是 `C1 + 额外正项` 的弱化，不能推出 `M_ss≥0`；
* 若 `H_v` 是 wild/finite 值且确实不含 buffer，则 C2 的 buffer 也只是**辅助正项**，除非能证明
  它对应 M 中某个未写出的项；文档没有这个恒等式；
* **判定 INVALID/PARTIAL**：循环性上没有等价目标，但作为目标证明引入了不在目标中的正项，
  属“把 buffer 当免费余量”的经典假证明；必须先删掉 buffer 重写 C2。

### C3（capsule/label weighting）
* `c_lana=(sF−1)/(2l)`，`thetaSumPaper=c_lana·A` 是**已证恒等式**（`Mzk1PaperNormThetaActual`）；
* draft 的 `(sF−1)A ≤ c_lana A` 只在 `A≤0` 或 `l≤1/2` 成立；对 A>0、l≥2 是**假不等式**；
* 修正的 `C3Pair` 把 `Σ(H−T)` 加回后，正性仍完全依赖 C1/C2，属于 identity-level，
  不提供任何独立于目标的非负性；
* **判定 IDENTITY-ONLY**（draft 写法 INVALID）；不能把 C3 当作“label 权重给出正性”的证据。

### C4（archimedean compensation）
* 这是最明确的循环点。`paperNormDeficit = LHS−RHS`（`Mzk1PaperNormMuActual.lean`），
  `PaperNormVerdict ↔ deficit ≤ 0`；若 `deficit := −Σ(H−T)`（即 `M = deficit+arch−torsion`），
  则 `M≥0` ⟺ `deficit ≤ arch−torsion`；
* `C4Bound` 写的是 `deficit ≤ arch`：
  - `torsion=0` 时与目标**逐字等价**（CIRCULAR）；
  - `torsion>0` 时只给更弱条件，**推不出** `M≥0`；
* doc 的“若 residual negative part at most arch，则 M≥0”是符号错误：应为 `≤arch−torsion`；
* **判定 CIRCULAR/INVALID**；禁止把 C4 当独立 arch 补偿。

### C5（wild 1/e buffer）
* 与 C2 同构：`(1/e)logp` 若已在 `H_p` 的 wild packet 中，则重复；若不在，则它不是 M 的项；
* 文档自己说“需要证明 H_p 确实含它”（steep requirement），说明当前没有独立证明；
* **判定 PARTIAL/INVALID（buffer 归属未定）**；不能作为非负性的独立来源。

### C6（G-constrained grouping）
* `C6Bound univ` 写成 `ΣT ≤ ΣH+arch−torsion`，而 `M_ss = Σ(H−T)+arch−torsion`；
  两者只差移项，**是目标的改写**；`c6_implies_M` 若用 `C6Bound univ` 就是循环；
* proper `S` 的版本（链 2 的 G1/G3 控制）不是等价目标，但它只控制 union 宽度，
  不提供逐项非负性；其 G1/G3 是**模型级**引理（`Mzk1Chain2CoreActual`），不是实际数据；
* **判定 CIRCULAR（univ）**；proper S 版单独标 MODEL-LEVEL/PARTIAL，不能混入“已证非负”。

## 3. 目标错配与已排除项

1. **目标错配 T1**：C1–C6 全部按 SSIneq wall `M=V−(sF−1)A` 写；framework 目标是
   `M_var=V+gap−(sF−1)A`，paper 目标是 `M_paper=A−R`。`gap` 由 `ind2Term` 定义
   （`Gap.lean:895`，C0 仍 CONDITIONAL）；未加 `gap` 的候选不能声称证明 variant/Cor312。
2. **目标错配 T2**：`C-MARGIN-FIX` 已指出 paper margin `A−R` **独立于 V/gap**；用 C1–C6 的 V/H/T
   去证 paper margin 必须先证明 `gap` 的恒等式，否则只是在证 SSIneq margin 的另一个表达式。
3. **已排除候选**：C3/C3b 的 `M0=log(deg φ)−0.15 logN` 是 route-B proxy（`C-MARGIN-FIX` §4），
   **不是** `A−R`；任何基于 M0 的分解/非负判定 **INVALID for paper target**，不进入本清单。
4. **不可用项**：`Mzk1PaperNormDeficitActual` 的 `deficit_cancel`/`deficit_nonpos_of_each_nonneg`
   只能作为 deficit 的代数重排（`deficit<=0 ↔ M>=0`），**不能**作为“每项非负”的来源；
   若证明某候选时调用 `PaperNormVerdict`/`SSIneq`/`variant`，立即标 CIRCULAR。

## 4. 结论与审查 gate

**总判定**：
* **CIRCULAR**：C4（`torsion=0`）、C6（`S=univ`）；
* **INVALID/PARTIAL**：C2/C5（buffer 不在 M 分解）、C4（`torsion>0` 符号）、C3（draft 假不等式）；
* **PARTIAL/OPEN**：C1（局部定义形式独立，但不足且 H_v 可为负）；
* **IDENTITY-ONLY**：C3 修正版；
* **没有任何候选**同时满足“严格强于目标 + 非负证明只用局部定义/已证引理 + 已证明”；
  当前 C1/C2/C5 仍是 open arithmetic，C4/C6 是目标改写，C3 是恒等式。

**入 Lean/证据链前的 gate（建议写进 `coord/DECOMP-PAIRING-CANDIDATES.md` 头部）**：
1. 每个候选必须给出 `def` 的完整类型、`M` 的哪个口径（`M_ss/M_var/M_paper`）、以及
   `candidate → 0≤M` 的**显式推导**；
2. 非负性证明的依赖闭包中**不得出现** `SSIneq`、`PaperNormVerdict`、`paperVerdict`、
   `variant`/`VariantData` 或任何与目标等价的定义；出现即 CIRCULAR；
3. 任何额外正项（tame/wild buffer、arch、torsion 调整）必须能在 `M` 的分解式中找到对应项；
   找不到即 INVALID（C2/C5 当前状态）；
4. `torsion` 符号必须显式：目标需要 `deficit≤arch−torsion`，不是 `deficit≤arch`；
5. 只有 C1 型局部不等式（H_v 非负已证）才可进入“每项非负”证明；目前 `H_v` 在 ramified 处
   为负，必须先给出 place 分解/符号域，否则只能记为 OPEN。

## 5. 一句话回报

**C4/C6 是目标的改写（CIRCULAR）；C2/C5 把不在 M 中的 buffer 当余量（INVALID/PARTIAL）；
C3 是恒等式且 draft 假；C1 形式独立但不足且未证。当前没有任何候选可作 M≥0 的独立非负来源。**
