# DECOMP-ROUND2-AUDIT — 第二轮分解文档复审（A1035）

日期：2026-11-12。**Status: READ-ONLY AUDIT；不编译、不新增 Lean。**
标准：`coord/DECOMP-AUDIT-TEMPLATE.md`（A–F 要件、§2 清单、§3 初审格式）。
对象：`DECOMP-ALGEBRAIC.md`、`M-MLINEAR-TERMS.md`、`IND2-CLOSURE.md`、`IND123-GLOBAL.md`、`LIT-VARIANT-DERIVATION.md`。

## 0. 复审口径

模板要求区分：**CIRCULAR**（分解/非负链假设了目标或目标等价物）、**INVALID**（公式/量化/符号错误，或把不在 M 中的项当余量）、**PARTIAL**（模型级/条件级/缺要件）、**PASS**（要件齐全且不作为定理使用）。

五个文档均无 Lean 文件进入本轮（只读文档；`LIT-VARIANT-DERIVATION` 的 Lean 草案含 `sorry` 占位，非生产文件）。
因此本轮的 PASS 只能是“模型/分析级诚实、并未冒充定理”；任何“DECISION/无条件”字样都要按内容降级。

## 1. 总表

| 文档 | 状态行 | 恒等式/来源 | 归一化 | arch/torsion | 每项非负 | 循环性 | sorry/gate | 判定 |
|---|---|---|---|---|---|---|---|---|
| `DECOMP-ALGEBRAIC` | 有（DECISION） | ⚠ 公式 `M=A+rhs`、`rhs_lin` 的来源不全；`Kbar'` 未定义 | ⚠ 未完全对齐 nC/权重/ℓ | ❌ arch/torsion 未列入 Kbar' | ❌ `Kbar'` 有界未证；floor/ceil 混用 | ✅ 未直接假设目标；但结论是**相对 Kbar' 的条件断言** | 无 Lean | **PARTIAL** |
| `M-MLINEAR-TERMS` | 有（PARTIAL） | ✅ 逐项引 lana 行；状态自标 PARTIAL | ✅ A/sF/j² 口径给出 | ✅ arch/shell 有界项已列 | ⚠ 负项清单有，但 literal-min 正性依赖未证读法 | ✅ 未假设目标；但“唯一自洽=min”是模型选择 | 无 Lean | **PARTIAL** |
| `IND2-CLOSURE` | 有（DECISION） | ✅ 引 IndAut/ThetaRegion/Gap 行 | ✅ 模型 n=1/e=1/shell=O 明写 | ✅ arch 未涉；模型无 torsion | ⚠ `variant_lit_stable` 用 `gapLitModel` 定义；`V≥0` 未证 | ⚠ 模型结论非循环，但“警报解除”是模型级 | 无 Lean | **PARTIAL** |
| `IND123-GLOBAL` | 有（DECISION） | ✅ 引 IndAut/ThetaRegion/Ind3/Gap 行 | ✅ iv/lit 集合选择明确 | ✅ arch 未涉 | ⚠ `V q-无关`/`A 无界` 未给证明或 admissible 序列 | ⚠ “iv 不稳定”是读法/模型条件结论，非定理 | 无 Lean | **PARTIAL** |
| `LIT-VARIANT-DERIVATION` | 有（DECISION） | ✅ 引 ThetaRegion/Gap/VcI 行 | ✅ lit=`univ` 明确 | ✅ A≥0 来源在草案中列 GAP | ❌ “lit variant 无条件可证”依赖 `V≥0` GAP-VNONNEG | ⚠ 非循环，但把条件结论写成平凡结论 | 草案含 `sorry` 占位（非生产） | **PARTIAL（有 overclaim）** |

## 2. 逐文档审查

### 2.1 `DECOMP-ALGEBRAIC.md` — PARTIAL

**可取**：
* 正确分离 `A=m logp/(2l)`、`qScale_j=j²A`、`Σj²=nC·sF`；`sum_jsq_eq_nC_mul_sFactor` 为 green；
* 正确指出 `(1−sF)x_1` 随 m 线性负、`mean(frac)` 有界，因此 floor/frac 本身不能抵消线性负项；
* 权重拆分后每项同号（`(1−sF)A w_j`）的观察正确；
* 结论把它定位为“需另一个 ∝m 正项或 UB”，没有直接声称 abc/变体已证。

**要件缺口（模板 §1）**：
1. **恒等式来源**：`M=A+rhs` 仅引 `rhs=-R`；`rhs_lin=(1/nC)Σ(−x_{j_i}logp)` 的推导未给 lana 行/引理，是 **MODEL 假设**；
2. **`Kbar'` 未定义**：把它写成“tame/arch/ind2 等剩余项”，但未给完整分解式或上界来源；
   “`Kbar'` 有界”只对 `shellDefect+orderVol` 引 VcI:313-319，**不覆盖**所有剩余项；
3. **floor/ceil 混用**：§3 写 `n_j=floor` 或 `ceil`，但 §4/§6 的 `mean(frac)∈[0,1)` 只对 floor 成立；
   ceil 时 `frac∈(-1,0]`，符号论证反转；§6 的 Lean 用 `Int.fract`（floor）但未声明“只取 floor 读法”；
4. **归一口径**：`x_1=m/(2l)` 是单 place/weight1；一般权重/多 place 未对齐（模板 §1-A4）；
5. **arch/torsion**：完全未进入 `Kbar'` 的显式分解，模板 §1-A5 的边界项缺失。

**循环性（a）**：
* 该分解**没有**直接假设 `M≥0`/`SSIneq`；`M` 是 paper margin 定义，不构成 CIRCULAR；
* 但 `M = logp[(1−sF)x_1+mean frac]+Kbar'` 若把 `Kbar'` 定义为“M 减去线性/frac 后的残差”，则是**定义性恒等式**，不能反过来证明残差有界或符号；
* 结论“大 m 时 M→−∞，除非 Kbar' 含 ∝m 正项”是**条件断言**，不是代数定理；作为“纯代数恒等式”标题过强。

**判定：PARTIAL**（不是 CIRCULAR；但恒等式来源/边界项/ceil 情形/Kbar' 有界均缺；若被当作“M<0 的实际证据”则升级为 INVALID，因为它是模型公式）。

### 2.2 `M-MLINEAR-TERMS.md` — PARTIAL

**可取**：
* 明确列出源中两个 m-线性项：`+A` 与 `−sF·A`（引 `IdentifiedCopies:441-456` green）；
* 明确指出 `ind2/shellDefect/orderVol` 只有 `O(3+loge)` 界、非 m-线性；
* 明确平均读法下 `dM/dm=(logp/2l)(1−sF)<0`，并承认这会产生大 m 反例；
* 状态行已写 PARTIAL，未把 qpilot 数值当证明（§4 仅对应）。

**缺口/风险**：
1. “唯一自洽解释 = literal-min(Ind1) 读法”是**模型/解释选择**，不是从 lana 证明的定理；
   `min_l j²=1` 的 label 存在性、`m_eff≤sF m` 均未证明（§5 自己列为待证）；
2. 若用 literal-min 得到 `dM/dm=0, M≥0`，需 `M_lead=0` 与有界正项都成立；文档未给完整证明；
3. `M=A+rhs` 的 `rhs` 来源链只给部分行（Gap:747-756 等），`logVol_lgp_integral=-sF*A` 是 green，但把它等同 `rhs` 平均仍需恒等式（与 `IND2-CLOSURE` 的模型值一致不等于实际）；
4. “不存在第三个 m-线性正项”依赖对源中所有项的枚举；`archDefect/shellDefect` 只是“有界”，但 `rhs` 中是否还有未被列出的线性项未排除。

**判定：PARTIAL**（模型级负结果有价值；但“唯一自洽=min”与 literal-min 正性未证，不能作为 variant 稳定/不稳定的证据）。

### 2.3 `IND2-CLOSURE.md` — PARTIAL（模型级，非定理）

**可取**：
* 明确限制 `K=Q_p, n=1, e=1, shell=O`；
* 逐项给出 `ind2` 的 iv/lit 计算（`ind2_iv=0`、`ind2_lit=j²A`），并引 IndAut/ThetaRegion/Gap 行；
* 明确 `iv` 与 `lit` 的差别来自 `S` 选择，且 `concreteVariantData` 用 iv；
* 明确指出数据（M−A 负相关）与模型冲突，列 GAP-DATA；
* `variant_lit_stable` 的 Lean 草案只依赖 `gapLitModel` 定义，未冒充 lana 定理（但仍需标 MODEL）。

**风险**：
1. 标题/结论 “variant 稳定，I_n 警报在该模型下解除”是**模型结论**，不能外推到实际 `concreteVariantData`；
2. `variant_lit_stable` 的证明用 `gapLitModel=sF*A`（定义），是**在模型内**的恒真；若把它当“variant 已证”则 CIRCULAR/overclaim；
3. `variant_iv_fail` 只给 `j²A>A` 的模型算术，未证明实际 iv 数据存在 `j≥2`、`A>0` 的 admissible 序列；
4. `V q-independent` 在该模型下取 V=0，未证明一般 `V` 的 q-无关性。

**判定：PARTIAL**（模型级诚实有限制说明；但“解除警报/稳定”不能进证据链；需要实际数据的 iv/lit 选择 + V≥0/无界序列证明）。

### 2.4 `IND123-GLOBAL.md` — PARTIAL

**可取**：
* 引 `IndAut:288-310`、`ThetaRegion:236-241/271-286`、`Ind3:122-134/213`、`Gap:502-545`，说明 indAut 无跨 capsule/label 置换；
* 明确 Ind1 通过 `thetaPilotOn S` 的集合 `S` 编码；Ind3 只是上界；
* 明确区分 iv/lit：iv `gap=0`、variant ⇔ `V≥(sF−1)A`；lit `gap=sF A`、variant 平凡；
* 结论提出“若 paper variant 应为真，则 lana 形式化/rhs 归一化必有偏差”，作为**待决策点**而非已证定理。

**风险**：
1. “iv 无 min/平均补偿 ⇒ q-不稳定的结论站得住”依赖 **V q-无关** 与 **A 无界**；文档只给结论，未给 `V q-无关` 的证明/引理，也未给 admissible 数据序列；
2. `variant_iv_iff` Lean 草案直接写成 `Corollary312Variant (concreteVariantData D) ↔ V+gap≥(sF−1)A`，但 `gap=0` 是模型结论，不是已证 lana 恒等式；
3. 对 `paper variant` 的偏差判断是**条件性**的（“若应为真”）；不能写成“已定位偏差”；
4. lit 平凡结论与 `LIT-VARIANT-DERIVATION` 相同，依赖 `V≥0` GAP，未在本文件证明。

**判定：PARTIAL**（源级阅读正确、无循环假设；但 iv 不稳定的前提未完全显式/未证；不能作为“variant 不稳定”的定理）。

### 2.5 `LIT-VARIANT-DERIVATION.md` — PARTIAL（有 overclaim）

**可取**：
* 精确定义 `ivLabels`/`litLabels`、`thetaFiniteOn`、`rhsDataLit`、`concreteVariantDataLit`；
* 给出 lit 的 `rhs_lit=V`、`gap_lit=sF·A`、`variant_lit ⇔ V≥−A` 的模型推导；
* 明确 `V≥0` 是 **GAP-VNONNEG**，并列出 `HULL-LIT=VC`、`GAP-LIT-ID` 两个 GAP；
* 明确 lit variant 无深层内容，ABC 实质在 iv。

**overclaim（b）**：
* Status 写 “lit variant **平凡真** / 无条件可证”，但正文 §3/§5 依赖 `V≥0`（GAP-VNONNEG）、`rhs_lit=V`（HULL-LIT=VC）、`gap_lit=sF*A`（GAP-LIT-ID）；
  三个引理都未证；Lean 草案中 `sorry` 明确标 GAP；因此 **不能把 lit variant 当已得结论**；
* “因 V≥0 只需 A≥0”是条件句，不是无条件证明；`V≥0` 的来源 `logShellRadius≥0` 仍需 green 端口；
* `V` 是否可为负取决于 `hullPacket` 的 ramified/finite 项；文档把它当作待证 GAP，方向正确，但 Status DECISION 与“无条件”措辞不一致。

**判定：PARTIAL**（lit 平凡性只能作为“待证三引理 ⇒ 平凡”的条件结论；不能进证据链为定理；若报告为“lit variant 已证”则 INVALID）。

## 3. 专项检查

### (a) frac 分解是否循环？
**不是 CIRCULAR，但它是定义性/条件性分解，不能当独立符号证明。**
* `x_j=n_j+frac(x_j)`、`n_j=floor(x_j)` 是定义展开；`M` 的表达式若把 `Kbar'` 定义为残差，则恒等式是**同义反复**，不提供 `Kbar'` 的有界性；
* 结论“frac 不能抵消线性负项”本身正确（`mean(frac)` 有界），但它只说明 **floor/frac 项** 无补偿；不能排除 `Kbar'` 中含 ∝m 正项——文档也承认需另一个正项；
* 若把 `Kbar'` 的界当作已知（`shellDefect` 界），只覆盖 `shellDefect+orderVol`，不是全部 Kbar'；
* **ceil 读法**下 `frac∈(-1,0]`，`mean(frac)` 可为负，符号结论不成立；文档 floor/ceil 混用，必须固定 floor 或分情形。

### (b) lit 平凡结论是否被当成结论？
**是，但被 GAP 削弱，不能作为已证结论。**
* `LIT-VARIANT-DERIVATION` 的 Status/§3 写 “lit variant 平凡真/无条件可证”；
* 实际链：`rhs_lit=V`（GAP HULL-LIT=VC）、`gap=sF A`（GAP GAP-LIT-ID）、`V≥0`（GAP-VNONNEG）；
* 三个 GAP 任一未证，lit variant 不是无条件结论；只能标 **条件定理**：`HULL-LIT=VC + GAP-LIT-ID + V≥0 ⇒ lit variant`；
* `IND2-CLOSURE`/`IND123-GLOBAL` 的 “lit variant 平凡” 同此限制；不能拿它作为实际 `concreteVariantDataLit` 的 green 结论。

### (c) iv 不稳定论断的前提是否显式？
**部分显式，但不完整。**
* 已显式：iv 读法 `S={j}`、`K=Q_p,n=1,e=1,shell=O`（IND2 §1），`concreteVariantData` 用 iv（IND2 §5），lit 用 `univ`（IND123 §5）；
* 未显式/未证：`V` q-无关（需 `logVol_hull_vcI` 的 q-无关性证明）、`A` 无界（需 admissible 数据序列 `m→∞`）、`gap_iv=0`（模型推导，非 lana 恒等式）、`j≥2` capsule 在实际数据中存在；
* 结论 “iv 不稳定” 应写成：**在模型 (n=1,e=1,shell=O, iv 读法) + V q-无关 + A 无界 + j≥2 存在 下，variant 失败**；缺一不可。

## 4. 判定与 gate

| 文档 | 判定 | 主要理由 | 能否进证据链 |
|---|---|---|---|
| DECOMP-ALGEBRAIC | **PARTIAL** | 模型恒等式/残差 Kbar' 未定义；ceil/floor 混用；仅条件结论 | 否（研究记录） |
| M-MLINEAR-TERMS | **PARTIAL** | m-线性枚举正确；literal-min 救援未证、是读法选择 | 否（模型记录） |
| IND2-CLOSURE | **PARTIAL** | 最小模型内计算；variant 稳定是模型结论；数据冲突已列 | 否（模型记录） |
| IND123-GLOBAL | **PARTIAL** | 源级 Ind 结构分析；iv 不稳定前提未完全证明 | 否（条件/模型记录） |
| LIT-VARIANT-DERIVATION | **PARTIAL（overclaim）** | lit 平凡依赖 3 个 GAP；“无条件可证”措辞过强 | 否（条件记录） |

**Gate（按模板 §1-C/§2）**：
1. 任何声称“lit variant 已证”的文档必须补齐 `HULL-LIT=VC`、`GAP-LIT-ID`、`V≥0` 三个引理的 green 证据；否则只能标 CONDITIONAL/PARTIAL；
2. 任何声称“iv 不稳定/大 m 反例”的结论必须给出：iv 读法、模型限制、V q-无关、A 无界、j≥2 admissible 序列；缺一即 PARTIAL；
3. `DECOMP-ALGEBRAIC` 进入 Lean 前，`Kbar'` 必须有完整 `def` 与上界来源；floor/ceil 必须固定；
4. 以上五文档均无 watchdog 结果；按 A986/A988 只能写 PENDING-WATCHDOG/MODEL，不得写 PROVED/green；
5. 本轮**未发现直接假设 M≥0/SSIneq 的 CIRCULAR 证明**；主要问题是模型/条件被写成 DECISION、GAP 被低估，以及 `Kbar'`/literal-min 的解释选择未证。

## 5. 一句话结论

**五篇均为模型/条件级：DECOMP-ALGEBRAIC、M-MLINEAR-TERMS、IND2-CLOSURE、IND123-GLOBAL、LIT-VARIANT-DERIVATION 全判 PARTIAL；无 CIRCULAR 目标假设，但 lit 平凡性与 iv 不稳定性都被写成比实际更强的结论，必须降级为 GAP-条件陈述。**
