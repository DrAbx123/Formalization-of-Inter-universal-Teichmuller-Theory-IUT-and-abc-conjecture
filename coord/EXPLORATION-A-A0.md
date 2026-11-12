# EXPLORATION-A-A0 — Calegari–Dimitrov–Tang holonomy 界：原始陈述抄录

日期：2026-11-12。

**Status: LITERATURE V2. Phase: A0 PASS**（精确陈述已取得、双版本互核；无未核实内容进入 A1）。

## 1. 做了什么

1. 下载并解析原文两份（不用记忆）：
   * F. Calegari, V. Dimitrov, Y. Tang, *The Unbounded Denominators Conjecture*,
     J. Amer. Math. Soc.（in press），PDF: `https://math.berkeley.edu/~ytang/UDC.pdf`；
     arXiv:2109.09040v4, DOI 10.48550/arXiv.2109.09040；
   * V. Dimitrov, *Holonomy rank bounds for the unbounded denominators conjecture*,
     IAS Arithmetic Groups seminar, 17 Nov 2021, slides,
     `https://www.ias.edu/sites/default/files/Holonomy.pdf`（arXiv:2109.09040v1 的讲义版）。
2. 用 pypdf 抽取全文，逐条定位 `Theorem 2.0.1`、`Definition 2.0.4`、`Corollary 2.0.5`、
   `Theorem 5.1.4`、`Theorem 7.2.1`、`Theorem 7.3.3`、`Proposition 3.0.1` 的原文，
   并与讲义版互核；arXiv v4 与 JAMS PDF 的定理编号/陈述一致。
3. 未找到独立发表的更强 holonomy 界后续论文；文内 §7.3 的 vector-valued 版本
   是该文自身的后续推广，另有文内注记（alternate proof）把常数 `e` 改进为 `2`。
   因此 A0 采用原论文的陈述，不引用未核实的“后续改进”。

来源落盘（工作区）：`tmp/lit/UDC-arxiv-v4.pdf(.txt)`、`tmp/lit/Holonomy.pdf(.txt)`、
`tmp/lit/UDC.pdf(.txt)`。

## 2. 数据表（精确陈述，逐字转述）

### 2.1 抽象定理（Theorem 2.0.1）

> Consider the following data:
> (i) a nonconstant rational function `p(x) ∈ Q(x) ∖ Q` without pole at `x = 0`,
> (ii) a formal power series `x(t) ∈ t + t²Q[[t]]` pulling back `p` into an integral
>      coefficients power series `x* p := p(x(t)) ∈ Z[[t]]` in the new variable `t`,
> (iii) and a holomorphic mapping `φ : D(0,1) → C` taking `φ(0) = 0` with `|φ′(0)| > 1`,
>       and pulling back `p` into a holomorphic function `φ* p ∈ O(D(0,1))` on some
>       neighborhood of the closed unit disc.
> Suppose the formal power series `f₁,…,f_m ∈ Q[[x]]` are `Q(p(x))`-linearly independent
> and satisfy `x* fᵢ ∈ Z[[t]]` and `φ* fᵢ ∈ O(D(0,1))`.
> Then `f₁,…,f_m ∈ Q(x)` are algebraic, and
>
>   `m ≤ e · ( ∫_T log⁺|p∘φ| dμ_Haar ) / log|φ′(0)|`,   (2.0.3)
>
> where `e = 2.718…` is Euler's constant.

（原文 Theorem 2.0.1，JAMS PDF p.9；arXiv v4 p.7-8。这里 `T` 是单位圆，`μ_Haar` 是
归一化 Haar 测度，`log⁺ = max(log,0)`。）

### 2.2 分母类型/全纯性定义（Definition 2.0.4）

> For `U ⊂ C` open, `R ⊂ C` a subring with fraction field `F := Frac(R)`, and
> `x(t) ∈ tQ[[t]]`, `H(U, x(t), R)` is the ring of formal power series `f(x) ∈ F[[x]]`
> whose `t`-expansion `f(x(t)) ∈ R[[t]]`, and such that there exists a nonzero linear
> differential operator `L` over `Q(x)` with `L(f) = 0` and having a trivial local
> monodromy around all of its singular points that belong to `U`.
> `V(U, x(t), R)` is the `F(x)`-vector space spanned by `H(U, x(t), R)`.
> For `x(t) = t`: `H(U, R)`, `V(U, R)`.

“Trivial local monodromy” 的定义（同页）：存在 `U_α ∋ α` 与 `n` 个 `U_α` 上亚纯函数
`g₁,…,gₙ`（`n = ord L`），在 `U_α ∖ {α}` 上构成 `L(f)=0` 解空间的 C-基。

### 2.3 Holonomy rank bound（Corollary 2.0.5）

> Let `0 ∈ U ⊂ C` be an open subset containing the origin. If the uniformization radius
> of the pointed Riemann surface `(U,0)` is strictly greater than `1`, then the algebra
> `V(U,Z)` is finite-dimensional as a `Q(x)`-vector space.
> More precisely, let `p(x) ∈ Q(x) ∖ Q` be a nonconstant rational function without poles
> in `U`, and let `φ(z) : D(0,1) → U` be holomorphic with `φ(0)=0`, `|φ′(0)|>1`.
> If `x(t) ∈ t + t²Q[[t]]` has `p(x(t)) ∈ Z[[t]]`, then
>
>   `dim_{Q(p(x))} V(U, x(t), Z) ≤ e · ( ∫_T log⁺|p∘φ| dμ_Haar ) / log|φ′(0)|`.  (2.0.7)

（JAMS PDF p.10；arXiv v4 p.8。注意这里是 `V(U,x(t),Z)`，即系数分母型 `R=Z`；
Puiseux 情形见 Theorem 7.2.1 的 Remark 7.2.2：把 `Z[[x]]` 换成
`Z[λ(τ/m)/16]⊗C` 型条件。）

### 2.4 应用侧 uniformization radius（Theorem 5.1.4）

> The conformal size `|F′_N(0)|` (Riemann uniformization radius of `C ∖ μ_N`) is
>
>   `|F′_N(0)| = γ_N := 16^{1/N} · Γ(1+1/(2N))² Γ(1−1/N) / ( Γ(1−1/(2N))² Γ(1+1/N) )`,   (5.1.5)
>
> with expansion
>
>   `γ_N = 16^{1/N} ( 1 + ζ(3)/(2N³) + 3ζ(5)/(8N⁵) + O(N⁻⁶) )`,   (5.1.6)
>
> where the remaining `O(N⁻⁶)` is a positive real number.

（JAMS PDF p.35；arXiv v4 p.34-35。`F_N : D(0,1) → C∖μ_N` 为 universal covering map，`F_N(0)=0`。）

### 2.5 应用判定（Proposition 3.0.1）

若 (1) `|F′_N(0)|` 渐近至少 `16^{1/N}(1 + A/N³)`（某 `A>0`），且
(2) 固定 `B>0` 有均值界 `∫_{|z|=1−B N⁻³} log⁺|F_N| dμ_Haar ≪_B log N / N`，
则 `Q(λ)`-向量空间 `R_{2N}`（Fourier 系数在 Q、在 `i∞` 有界分母、各处 cusp width 整除 `2N` 的模函数）
维数 `≤ C N³ log N`（绝对常数 C）。

### 2.6 ODE/vector-valued 形式（后续推广）

> **Theorem 7.2.1.** Let `f(x) ∈ Z[[x]]` be an integer coefficients formal power series
> solution of `L(f)=0`, where `L` is a linear differential operator without singularities
> on `P¹ ∖ {0, 1/16, ∞}`. If the `x=0` local monodromy of `L` is finite, then `f(x)` is
> algebraic, and more precisely `f(λ(τ)/16)` is automorphic for some congruence
> subgroup `Γ(N)` of `SL₂(Z)`.

> **Theorem 7.3.3.** Let `(F,ρ)` be a vector-valued modular form for `PSL₂(Z)` of
> dimension `n` and weight `k`. Suppose that some component `F_j(τ)` has at `τ=i∞`
> a formal Fourier expansion lying in `Z[[q]] = Z[[e^{πiτ}]]`. Then `F_j(τ)` is a
> classical modular form of weight `k` on a congruence subgroup of `SL₂(Z)`.

（JAMS PDF p.62/65；arXiv v4 p.51/54.）

### 2.7 常数与分母类型汇总

| 项 | 值/类型 | 出处 |
|---|---|---|
| 常数 | `e = 2.718…`（Euler） | Thm 2.0.1 (2.0.3) |
| 分母类型（抽象） | `R = Z`；`f(x(t)) ∈ Z[[t]]` | Def 2.0.4, Cor 2.0.5 |
| 分母类型（Puiseux） | `f(λ(τ)/16) ∈ Z[[λ(τ/m)/16]]⊗C` | Thm 7.2.1 + Rem 7.2.2 |
| 参数 | `p(x)∈Q(x)∖Q`, `x(t)∈t+t²Q[[t]]`, `φ(0)=0`, `|φ′(0)|>1` | Thm 2.0.1 |
| 局部单值 | `x=0` monodromy finite order `N`；`U` 上其余 singular 平凡 | Thm 7.2.1, Def 2.0.4 |
| 维数上界 | `m ≤ e·∫_T log⁺|p∘φ| / log|φ′(0)|` | (2.0.3)/(2.0.7) |
| 应用判据 | `γ_N` 下界 + 均值界 ⇒ `dim ≤ C N³ log N` | Prop 3.0.1 |
| 常数改进（文内） | 另一证明可把 `e` 改进为 `2`（不是独立论文） | 原文 §2.5 末注 |

### 2.8 E-table（外部陈述登记，供 A2/A3 引用）

| ID | 陈述 | 出处 | 状态 | 用途 |
|---|---|---|---|---|
| E1 | Theorem 2.0.1（抽象 holonomicity 上界） | UDC arXiv:2109.09040v4 p.7-8；JAMS PDF p.9 | LITERATURE_VERIFIED | A2/A3 映射 |
| E2 | Definition 2.0.4（`H/V(U,x(t),R)` 与平凡局部单值） | 同上 p.8-9 | LITERATURE_VERIFIED | 分母类型 |
| E3 | Corollary 2.0.5（holonomy rank bound, `R=Z`） | 同上 p.9 | LITERATURE_VERIFIED | A3 上界 |
| E4 | Theorem 5.1.4（`γ_N` Gamma 闭式/`ζ` 展开） | UDC arXiv v4 p.34-35 | LITERATURE_VERIFIED | A1 共形半径 |
| E5 | Theorem 7.2.1 / 7.3.3（ODE/vector-valued 推广） | 同上 p.51/54 | LITERATURE_VERIFIED | 后续工作 |
| E6 | Belyi `β(z)=4z/(1+z)^2` 仓库对象（不作为外部定理） | `Mzk1BelyiCanonicalActual`（src sha C94525DB…，olean=True）、`Mzk1BelyiCvBridgeActual`（E1C7945C…）、`Mzk1BelyiMaximizerActual`（C64236AC…） | PINNED_FILES（ole=True；probe `_A924BelyiPinProbe` EXIT=0，key decls trio `[propext, Classical.choice, Quot.sound]`） | A2 F4 形状 |

## 3. 与判定条件的对照（A0 判定）

* **试金石 defer**：A0 是文献抄录阶段，不提出任何 abc 全称主张；Q1–Q4 全部 defer 到 A3（那里给量词范围、`3^k−1` 信息进入点、丢失检验）。A0 不以“抄到定理”冒充路线 A 的数学结论。
* A0 要求：“取得原文中 holonomy 界的精确陈述：假设、分母类型、上界公式。”
  **已满足**：Theorem 2.0.1 + Corollary 2.0.5 给出全部假设、`R=Z` 分母类型和 (2.0.3)/(2.0.7)
  的精确上界；`Definition 2.0.4` 给出 `H/V` 的严格定义；`Theorem 5.1.4` 给出 `γ_N` 的闭式。
* 未核实项已显式标注：没有找到独立发表的更强 holonomy 界；§2.5 文内注记的常数 `2` 不是
  独立定理，未在 A0 当作外部输入。
* 因此 A0 **不停止**，进入 A1（用 `x = λ/16` 例子校准上界数值）。

## 4. 下一步或停止：A1 需要计算/核对的量

1. **共形半径/ uniformization radius**：`|φ′(0)|`；对 `C∖μ_N` 用 `γ_N` 的 Gamma 闭式
   (5.1.5) 或展开 (5.1.6)；A1 例 `x=λ/16` 需 `λ` 的共形半径 `λ′(0)=16` 及
   Belyi 映射预复合后的 `|φ′(0)|`（讲义版给出 `4 → 16` 的 passage）。
2. **增长积分**：`∫_T log⁺|p∘φ| dμ_Haar`（Nevanlinna 特征/均值）；对 `F_N` 用
   Theorem 6.0.1 的 `O(log N/(1−r))` 型均值界（具体形式需按原文 §6 抄）。
3. **分母类型/整性项**：`R = Z` 或 `Z[1/N]`；必须核 `x* f_i ∈ Z[[t]]`、
   `f(λ(τ)/16) ∈ Z[[λ(τ/m)/16]]⊗C` 的精确形式（Rem 7.2.2）。
4. **ODE/局部单值**：`L` 的阶、`x=0` 的有限 monodromy 阶 `N`、其余奇异点的平凡性；
   以及 `p(x)` 在 `U` 上无极点、`φ* p` 在闭单位盘邻域全纯。
5. **维数/函数族**：`m`（`Q(p(x))`-线性无关函数个数）、`f_i` 的候选定义；A1 先只做
   原文 `x=λ/16` 单值化例子，计算 `共形半径`、`增长积分`、`上界` 三个数并与原文对照。
6. **常数**：`e=2.718…`；若文内注记的 `2` 被用于校准，必须标为“文内替代证明的注记”，
   不作为独立外部定理。

A1 的停止条件：三个数与原文对不上 ⇒ 管线有错，先修；对上了才进入 A2 设计三元组函数族。