# Task K memo — 证明论 / 自动证明 / Lean tactics 对当前 exact arithmetic-norm 引理的适用性

日期：2026-10-30（Asia/Shanghai）
范围：只做研究；不改目标、不写 surrogate、不把未证命题写成已证。
证据：所有 tactic 结论均来自本次实际运行的 Lean 探针（文件见 §1.3），失败即记录失败。
未运行项在 §7 单列。

---

## 0. 结论（TL;DR）

1. **纯算术 residue 可以自动化，但几乎每条都需要先给出“bridge 引理”，tactic 搜索本身不是瓶颈。**
   在 19 条与当前 exact 目标同形的算术命题上，无 hint 的 11-tactic portfolio
   （linarith / nlinarith / positivity / norm_num / gcongr / field_simp+ring /
   field_simp+linarith / omega / grind / aesop / simp）只直接闭合 8 条。
   对剩下 11 条，加入目标特定的 bridge 引理后**全部**可闭合（其中 G14 只核对了签名，
   见 §2.3 注）。例如：
   - `N/(2*l) ≤ N`：`linarith` 失败，`rw [div_le_iff₀ (by linarith)]; nlinarith` 成功；
   - `p^(-a) ≤ p^(-b)`：`gcongr` 失败，`Real.rpow_le_rpow_of_exponent_le hp.le (neg_le_neg h)` 成功，
     `grind [Real.rpow_le_rpow_of_exponent_le]` 也成功；
   - 有限和 `∑ j²`：任何单 tactic 都不行，`induction` + `Finset.sum_range_succ` + `ring` 成功；
   - 具体 `Fin 14` 和：`norm_num` 失败，`norm_num [Fin.sum_univ_succ]` 成功。

2. **项目层的 9 个 exact goal（含 4 个已有人工证明的）用同一个 portfolio 全部未闭合。**
   这说明自动化在当前 frontier 上能贡献的是“子目标清零”，不是“目标清零”。
   瓶颈是缺少具名中间引理 / carrier 归约，而不是 tactic 不够强。

3. **当前 exact 缺口的数学核心不是算术命题，ATP 原则上看不到它。**
   paper Θ-pilot hull log 与 q[2u]/root stack carrier 的缺口是：
   (a) hull 对象相等（测度 / 集合相等），(b) source 标识（`sourceQPilotSignedLog = localSignedLog C3.q`），
   (c) tensor norm carrier 的范数选择。三者都不是 `ℝ` 上的一阶算术命题，
   没有 RCF/Presburger/SMT 判定过程可作用。

4. **两个负面发现（重要，建议 lead 决策）：**
   - `S708ExactGoal`（p^(-N) 归一化）在 N>0 时与 `S717` 自己的 audit 一致地**不成立**：
     区域只给出 `‖x‖ ≤ p^(-N/(2l))`，而 `p^(-N/(2l)) > p^(-N)`。不要把它当 automation 目标。
   - `S720/S723.QVFamBlockNormPreserving`（tensor 坐标范数 = rootBase 域范数的等距性）
     在一般 `Module.finBasis` 下**不可证且很可能为假**。手算反例（未形式化，见 §3.4）：
     `K = Qp(√p)`，`x = p + √p`，`|x| = p^(-1/2)`，而 `finBasis {1, √p}` 的坐标 sup 范数 = 1。
     因此 `S717/S720/S723` 这一整条“tensor lattice norm”路线需要先修 carrier，而不是交给 ATP。

---

## 1. 环境与证据

### 1.1 环境
- Lean `4.32.2`，Mathlib `v4.32.2`（`lake-manifest.json`），本地 Mathlib oleans 8275 个、项目 oleans 2364 个。
- `polyrith`：**不可用**。Mathlib `Mathlib/Tactic/Polyrith.lean` 明写
  “The `polyrith` tactic relied on an external Sage server which has been shut down”，
  执行即抛错。即使可用也依赖 SageCell 网络，不能作为离线证明路径。
- SMT：无 `z3` / `cvc5` 可执行文件；`lake-manifest.json` 无 `lean-smt` 依赖。
  即：本项目当前没有 SMT oracle 可调用（且 NRA 在 SMT 中本来也只是启发式）。
- `sympy 1.14` 存在，但与 `polyrith` 无关（polyrith 不走本地 sympy）。

### 1.2 运行方式
所有探针用 `lake env lean <file>` 单文件编译；每个文件含多条 `example`，
Lean 在 elaboration 错误后继续处理后续 declaration，因此一次编译即可得到逐条 pass/fail。
探针文件位于 `tmp/sheaf/xif/paper/_taskK/`，日志位于 `tmp/sheaf/xif/paper/_taskK/out/`。

### 1.3 证据文件
- `C1_portfolio.lean` / `out/C1.log`：19 条算术 shape 的无 hint portfolio。
- `C2_detail.lean` / `out/C2.log`：33 条“目标 + 具体 tactic / 具体 bridge 引理”对照。
- `B_project.lean` / `out/B.log`、`B2_project.lean` / `out/B2.log`：项目层 9 个 goal。
- `T_*.lean` / `out/T_*.log`：12 个单 tactic 文件（首轮并行编译因资源竞争产生
  `.olean.private` 读取错误，未采用其结论；结论以串行 C1/C2/B/B2 为准）。

---

## 2. 实验矩阵

### 2.1 无 hint portfolio（C1）
19 条 shape 中直接闭合 8 条：
`Fin` 指标 `omega`、整数平方 `nlinarith`、`x²+1>0` / `rpow` 正性 `positivity`、
权重和 `simp`、`N/(2l) ≤ N/2`、`x/(x+1) ≤ 1`、`a ≤ |a|+|b|`。
未闭合 11 条：除法系数、rpow 单调/加法、有限平方和、具体 `Fin` 和、prime cast、field 恒等式、log 单调/非正。
（其中两条 field 恒等式其实被 `field_simp` 单独闭合，只是 portfolio 写成
`field_simp; ring`，`field_simp` 已无目标后 `ring` 报 “No goals to be solved”，
属于 harness 组合问题，不是能力问题——见 2.2。）

### 2.2 带 bridge 的 recipe（C2，逐条实测）
| goal shape | 失败的单 tactic | 实测成功的 recipe |
|---|---|---|
| `N/(2*l) ≤ N`（N≥0, l≥5） | linarith, gcongr | `rw [div_le_iff₀ (by linarith : (0:ℝ) < 2*l)]; nlinarith`；或 `field_simp; nlinarith` |
| `p^(-a) ≤ p^(-b)`（b≤a, 1<p） | gcongr | `Real.rpow_le_rpow_of_exponent_le hp.le (neg_le_neg h)`；`grind [Real.rpow_le_rpow_of_exponent_le]` |
| `p^(-(N/(2l))) ≤ p^(-(N/(4l)))` | gcongr | 同上 lemma，再用 `rw [neg_le_neg_iff]` + `div_le_div_of_nonneg_left hN (by positivity) (by nlinarith)` |
| `p^(-(a+b)) = p^(-a)*p^(-b)` | 全部 | `rw [show -(a+b) = -a + -b by ring, Real.rpow_add hp]` |
| `∑_{i<k}(i+1)^2 = k(k+1)(2k+1)/6` | norm_num, simp, nlinarith | `induction k` + `Finset.sum_range_succ` + `push_cast; ring` |
| 具体 `(1/14)∑_{i<14}(i+1)^2/58 = 5/4` | norm_num, simp | `norm_num [Fin.sum_univ_succ]` |
| `(1<p) : 1 < (p:ℝ)`（p prime） | positivity, norm_num | `exact_mod_cast (Fact.out : Nat.Prime p).one_lt` |
| `(N/(2*l))*(2*l) = N`；`N/(2*l)=N/2/l` | `field_simp; ring`（ring 无目标） | `field_simp`（单用即可） |
| `Real.log a ≤ Real.log b`（0<a≤b） | linarith | `exact Real.log_le_log ha hab`；`gcongr`；`grind [Real.log_le_log]` 三法均可 |
| `Real.log x ≤ 0`（0<x≤1） | gcongr | `Real.log_nonpos hx.le hx1`（签名核对；探针中误传 `hx` 属类型错误，未重跑） |

### 2.3 反例 / refutation 能力（实测）
- `paperThetaLinearCoefficient l = (l+1)/24`（S703/S704 的线性模型系数；S694 权重 1/l*、指数 j²/(2l)）。
- `l=29` 时该系数 = `(1/14)∑_{i=0}^{13} (i+1)²/58 = 5/4 > 1`：
  `norm_num [Fin.sum_univ_succ]` **实测闭合**。即 `GlobalPaperThetaComparisonGap` /
  `PaperThetaQpilotArithmeticInequality` 在 l=29 处是**假命题**，
  且 l≥29 的 prime 全部失败（l=23 时恰为 1）。
- 结论：ATP 可以**机器判定该 surrogate 为假**（这对“不要 surrogate”的路线是有用负结果），
  但不能把它变成真命题，也不能用它替代 paper hull 比较。

### 2.4 项目层（B/B2）
| 目标 | 状态 | portfolio 结果 |
|---|---|---|
| `S720.QVFamBlockNormPreserving` | exact | 未闭合；`intro x; simp only [qVFamBlockLinearEquiv]` 把目标化到 `‖x‖ = ‖(PiTensorProduct.subsingletonEquiv ()) x‖`，`rfl` 无效 |
| `S717.TensorFractionalLatticeNormLemma` | exact | 未闭合 |
| `S720.QVFamBlockMapsFractionalLattice` | exact | 未闭合 |
| `S708.S708ExactGoal` | exact（疑假，见 §3） | 未闭合 |
| `S712.RootImageRadiusLowerBound` | 已由 S727 证明 | — |
| `S718.RootThetaOneNormFormula` | 已由 S727 证明 | 未闭合（即使已有证明） |
| `RootQUnitNormLeOne`（S664） | 已证明 | 未闭合（即使已有证明） |
| `S730.QVFamBlockSMulCompatibility` | 已证明（`rw [map_smul]`） | 未闭合（即使已有证明） |
| `qVFamPaperRootCoefficient_le_normalized` | 已证明 | 未闭合（即使已有证明） |

要点：**已证明**的目标 portfolio 也闭合不了，因为证明需要 `rw`/`change` 到特定
lemma 的形状；这正说明当前缺口的瓶颈是“命名中间引理”，不是搜索深度。

---

## 3. 两个需要 lead 决策的负面发现

### 3.1 S708 的 p^(-N) 归一化是错的（与 S717 audit 一致）
`qPilotRootLabelRegion T b (oneSignedLabel) = F(N/(2l)) * O_hol ⊇ F(N/(2l))`，
所以自然上界是 `p^(-N/(2l))`。S708 要求 `‖x‖ ≤ p^(-N)`，而 `p^(-N/(2l)) > p^(-N)`（N>0, l≥5）。
S717 文件头已写明“using it for the root-label region would be a false normalization”。
**建议：S708ExactGoal 不作为目标；S712 的 p^(-N/(2l)) 形式才是自然形式。**

### 3.2 QVFamBlockNormPreserving 很可能为假（tensor 坐标范数 vs 域范数）
`FinitePadicTensor` 的范数由 `finitePadicTensorCoordinates` 诱导 = `finBasis` 坐标的 sup 范数
（`FinitePadicTensorTopology.lean` L52–58）；对 `Unit` 索引，
`subsingletonEquiv` 把它送到 `M ()` 的域范数。于是
`QVFamBlockNormPreserving` ⟺ “`Module.finBasis` 是 norm-orthogonal 基”。
手算反例（**未形式化**）：`K = Qp(√p)` 的归一化绝对值，基 `{1, √p}`，
`x = p + √p` 有 `|x| = p^(-1/2)`（因为 `N(p+√p) = p(p-1)`），
坐标 sup = `max(p^(-1), 1) = 1`。所以等距性不成立。
即使退一步只保留真实方向，也是 `‖equiv x‖ ≤ ‖x‖`（与本项目需要的方向相反）。
**建议：改 carrier 定义（把 tensor 块的范数取为经 `subsingletonEquiv` 拉回的局部范数，
则 S717/S723 变成 `rfl`），或把 norm 目标改成局部像 `‖equiv x‖ ≤ p^(-∑c)`（S724 的路线），
不要继续证等距。**

---

## 4. 证明论分析：为什么 ATP 只能碰到标量 residue

### 4.1 各 tactic 的逻辑强度
- `linarith`：线性有序域片段，证书由 kernel 检查；对该片段本质完备（先做 `ring_nf` 归一化）。
  失败通常表示目标不是线性推理的直接后承，或需要先消去除法（`div_le_iff₀` / `field_simp`）。
- `omega`：Presburger（ℕ/ℤ 线性）判定过程，完备；对 ℝ 目标无效（实测 `omega` 证不了 `-a ≤ -b`）。
- `nlinarith`：Positivstellensatz 风格的**启发式**证书搜索（预展开平方/乘积项），
  对非线性多项式片段**不完备**；成功与否依赖 hint 项（`sq_nonneg`、`mul_nonneg` 等）。
- `norm_num`：闭数值表达式的证书化简；可带 simp 引理（`Fin.sum_univ_succ`）展开有限和。
- `positivity`：符号启发式，不完备；对 `Real.rpow` 有专门扩展（`rpow_pos_of_pos`）。
- `gcongr`：单调性 lemma 的定向应用；不做除法/幂等非线性推理（实测对 `N/(2l)`、`p^(-a)` 均失败）。
- `grind`：E-matching + 同余闭包 + 线性算术的饱和式证明器；可用 `[lemma]` 提供 trigger。
  实测：给了 `Real.rpow_le_rpow_of_exponent_le` 后能闭合 rpow 单调目标；不给则不能。
  它不是判定过程，不产生非线性多项式证书。
- `aesop`：规则集最佳优先搜索，不完备；对分析/测度目标基本无效。
- `polyrith`：本环境**不可用**（上游已删除，依赖 SageCell）。
- SMT（cvc5/z3）：未安装；即便安装，LRA/LIA 可用而 NRA 只是启发式，
  且没有 `Real.rpow`/`Real.log`/测度/submodule 的理论。

### 4.2 判定性边界
- **在**判定边界内：线性实数算术（`linarith`）、Presburger（`omega`）、
  实闭域一阶理论（Tarski–Seidenberg，可判定但复杂度双指数，Lean 无实现）、
  多项式理想成员（Nullstellensatz；`polyrith` 若可用）。
- **不在**：含 `exp`/`log`/`rpow`（变指数）的一阶理论——Tarski 指数函数问题仍开放，
  更没有现成判定过程；本项目实际用的是“引理重写 + 线性/多项式 residue”，
  所以必须先有 `Real.rpow_*` / `Real.log_*` 的具名 bridge。
- **原则上不可自动化**：测度空间、Haar 测度、`Submodule`、张量积、函数空间上的等式/存在性；
  这些是二阶/高阶对象，不是 SMT 理论能表达的。当前 Cor3.12 主缺口（hull log 相等、
  source 标识、carrier 运输）正落在这一类。

### 4.3 一个可操作的判据
把目标写成 `∀ x, x ∈ S → ‖x‖ ≤ R` 或 `a = b` 时，先问：
1. 展开定义后是否只剩 `+`、`*`、`/`、`^`(ℕ)、`≤` 与 `rpow`/`log` 的**固定指数**？
   若是，按 §2.2 的 recipe 可自动/半自动。
2. 是否出现 `∑`、`∏`、`Finset` 指标？若是，先 `norm_num [Fin.sum_univ_succ]` 或
   `induction` + `Finset.sum_range_succ`，不要指望 `nlinarith`。
3. 是否出现 `Submodule`、`closure`、`Measure`、`≃ₗ`、`PiTensorProduct`？
   若是，ATP 只能闭合其中的标量 side goal，主体必须人工给结构引理。

---

## 5. 可执行策略（playbook）

### 5.1 分层策略
对每条 exact 目标强制分解为三层，禁止把整条目标丢给 ATP：
- **L0 scalar residue**：指数/系数/符号不等式。用 §5.2 的 recipe。
- **L1 bridge application**：`rpow`/`log`/`div`/prime 的具名引理。ATP 只负责 apply 后的 side goal。
- **L2 structural**：span 归纳、submodule 像、测度单调、carrier 运输。人工。

### 5.2 可直接复制的 tactic 片段
```lean
-- 系数除法
rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * l.value)]
nlinarith [Nat.cast_nonneg (α := ℝ) (qVFamily T b).order]

-- rpow 单调（负指数，底数 >1）
exact Real.rpow_le_rpow_of_exponent_le hp.le (neg_le_neg h)
-- 或带 trigger 的 grind
grind [Real.rpow_le_rpow_of_exponent_le, Real.rpow_add]

-- rpow 加法
rw [show -(a + b) = -a + -b by ring, Real.rpow_add hp]

-- 有限平方和
induction k with
| zero => simp
| succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

-- 具体 Fin 和 / 反例
norm_num [Fin.sum_univ_succ]

-- prime cast
exact_mod_cast (Fact.out : Nat.Prime p).one_lt

-- 除法恒等式（field_simp 单用；不要再接 ring）
field_simp

-- log 单调
exact Real.log_le_log ha hab        -- 或 gcongr / grind [Real.log_le_log]
```

### 5.3 hint 工程
- `grind [lemma1, lemma2]` 对“有引理但需要实例化”的目标最有效（实测 rpow 单调）。
  失败时先 `#check` 确认 lemma 的隐式参数能被 trigger 命中。
- `nlinarith [sq_nonneg _, mul_nonneg …, Nat.cast_nonneg _]`：hint 只加**会用到的**项；
  hint 过多会拖慢甚至改变搜索方向。
- `norm_num [Fin.sum_univ_succ]` 是评估具体 `Fin n` 和的正确入口；`decide`/`native_decide` 对 ℝ 无效。
- `gcongr` 只在目标是“函数单调 + 参数比较”时使用；对 `/` 和 `rpow` 不要先试它。

### 5.4 禁止事项（与项目纪律一致）
- 不把 `S708ExactGoal`、`S717.TensorFractionalLatticeNormLemma`、`S723.QVFamBlockNormPreserving`
  交给 ATP“再试试”：它们要么归一化错误，要么 carrier 可能为假。
- 不用 ATP 生成 `sorry`/axiom/空类型填充。
- 不因为某条 shape 被 `norm_num` 闭合，就宣称对应的 paper 命题已证。

---

## 6. 对当前 exact 缺口（paper Θ-pilot hull log 与 q[2u]/root stack carrier）的判断

### 6.1 哪些部分是算术、且已被/可被自动化
- `q[2u] = q^{1/(2l)}` 的系数归一化 `c_root = order/(2l)`：
  `QVFamRootFactorCorrectionActual` 已证；其算术子步（`(2l)*(N/(2l))=N`、
  `N/(2l) ≤ N`）都是 §5.2 的 recipe 可闭合的。
- `rootImageRadius = p^(-c_norm/(2l))`（S709）与 `RootThetaOneNormFormula`（S727）：
  已证，证明中的 `rpow` 代数步是 §5.2 形式。
- `paperThetaLinearCoefficient = (l+1)/24`：**假**（l≥29）；ATP 可 refute，不可证。

### 6.2 哪些部分不是算术、ATP 无贡献
- `paperPerBThetaHullLog` 与 `perBThetaHullLog` 的相等（S716 `PaperHullVsS663ThetaAverageGap`）
  被 S726 证明为**假**：左边 ≤0（hull 含于单位参考），右边 >0（label-1 项）。
  这是测度论 + 序论证，不是算术。
- `ConcreteSourceQIdentification`（`sourceQPilotSignedLog = localSignedLog C3.q`）：
  对象等式，需要 source 构造。
- `PaperXiFSourceLink` 四个字段（source_identifications、qPilotLogVolume_eq_paper、
  link_identification、link_implies_inclusion）：接口/数据，不是命题。
- hull 相等（`rootExtensionProductImageHull = paper holomorphic/lambda-O hull`）：
  集合/测度等式。

### 6.3 结论
Task K 能给 Cor3.12 主缺口提供的只有：
(i) 标量 residue 的自动闭合 recipe（§5.2）；
(ii) 对 surrogate 的机器 refutation（§2.3，证明“线性模型不可能对”）；
(iii) 对 `S708/S717/S720/S723` 这条 norm 路线的否定性判断（§3）。
主缺口本身（hull log / source / carrier）**不能**由 ATP 闭合，也不应该继续投入 tactic 搜索。

---

## 7. 未运行 / 限制（如实记录）

- 未跑全 Project build、未跑 axiom audit、未跑 comparator、未做最终验收。
- 未安装 z3/cvc5/`lean-smt`，因此**没有**实际运行任何 SMT solver。
- `polyrith` 未运行（上游已删除，运行即报错）。
- §3.2 的 `Qp(√p)` 反例是手算，**未**在 Lean 中形式化；它是“不可证/疑假”的分析依据，
  不是 kernel-checked 定理。
- G14（`Real.log_nonpos`）只核对了签名，未在修正参数后重跑。
- 首轮 12 个 `T_*.lean` 并行编译因资源竞争出现 `.olean.private` 读取错误，
  其结论**不采用**；采用串行 C1/C2/B/B2 的结果。
- 探针文件都在 `_taskK/`，未改动任何生产 Lean 文件；memo 之外无仓库改动。

---

## 8. 建议的下一步（给 lead）

**P0（阻断性，先决策）**
1. 决定 tensor 块范数：改为“经 `subsingletonEquiv` 从 `rootBase` 拉回的范数”
   （则 `QVFamBlockNormPreserving` 与 `TensorFractionalLatticeNormLemma` 变 `rfl`），
   或把目标改成 S724 的局部像形式 `‖equiv x‖ ≤ p^(-∑c)`。
   在此之前，**不要**再为 S708/S717/S720/S723 写证明或跑 ATP。
2. 把 `S708ExactGoal` 标记为“错误归一化”，消费者改用 S712 的 p^(-N/(2l)) 形式。

**P1（可立即自动化，产出小但真实）**
3. 用 §5.2 的 recipe 清理各文件的算术 side goal（系数、rpow 指数、prime cast、log 单调），
   每个文件可省 5–15 行；建议只改证明体，不改陈述。

**P2（研究，不承诺）**
4. 若要继续 hull log 比较：目标应是“paper hull log = rootNormHull 的归一化 log”
   的 carrier 等式，而不是标量平均；这需要 §6.2 的结构工作，ATP 无帮助。
5. 可把 §2.3 的 refutation 固化为一个小的 Lean 定理（`paperThetaLinearCoefficient l`
   的闭式 + `l ≥ 29` 时 >1），作为“线性 surrogate 不可行”的机器证据；
   这属于研究记录，不进入 Cor3.12 闭包。

---

## 附：本次探针的关键命令

```powershell
cd D:\lean
lake env lean tmp\sheaf\xif\paper\_taskK\C1_portfolio.lean
lake env lean tmp\sheaf\xif\paper\_taskK\C2_detail.lean
lake env lean tmp\sheaf\xif\paper\_taskK\B_project.lean
lake env lean tmp\sheaf\xif\paper\_taskK\B2_project.lean
```
