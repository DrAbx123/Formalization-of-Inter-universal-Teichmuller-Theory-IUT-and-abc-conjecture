# EXTERNAL-FINAL — 外部路线可行性矩阵 + A-local 工具清单

日期：2026-11-13；qpilot（A1102）。**文档汇总**；未跑 Lean。A/B/C 采用统一口径：

- **A**：目标（或明确子目标）可由**已证外部定理/标准显式公式**经具体映射推出；
- **B**：需要新的模型/定义/桥接，或只是等价重述，没有独立降低强度；
- **C**：只有类比/重命名，或对象不匹配，不能蕴含目标。

## 1. 总矩阵

| 路线 | 当前判定 | 能给什么 | 到 A/B 所需输入 | 来源 |
|---|---|---|---|---|
| **Deligne 小截面** | **B** | `deg≤0 ⇔ 存在小范数截面` 的 inf 重述；det bundle/Deligne pairing 工具 | arch 显式估计 + 有限位整性；形式化 det 度量 | FEAS-DELIGNE / OUTSIDE-DELIGNE |
| **熵/SSA** | **C**（B 仅条件） | 无可直接实例的熵不等式；目标不是熵差 | 需把 q/theta 体积识别为熵并证明 SSA 型不等式（硬内容） | FEAS-ENTROPY |
| **Pluripotential/Monge-Ampère** | **C**（B 仅重述） | 非阿 psh/metric 单调性、相对 volume 公式（1805.01016） | Berkovich 空间、psh envelope、MA 测度、det of cohomology；当前树无 | FEAS-PLURIPOTENTIAL |
| **Tropical/离散凸** | **C（exact）；B（grouped/error）** | modular `f_L/f_N`；`f_D` disjoint-subadditive | **全局** submodularity/L-凸（f_D 已有 6/179,970 Lovász 反例）+ 分组零 deficit | FEAS-TROPICAL / OUTSIDE-SUBMODULAR |
| **Brascamp–Lieb/Barthe/Borell/LSI** | **C**；单映射特例 **B（重述）** | 单线性映射的精确 `|det|` Haar 缩放（已有） | 需要真正的多投影系统；当前只有单映射 | FEAS-BRASCAMP |
| **Motivic/p-adic integration** | **C（global）；B（local monomial）** | 局部 valuation-ball/Haar 几何级数、tame logShell 公式 | Denef–Loeser/resolution、motivic measure、Ax–Kochen transfer + real log/arch 数据 | FEAS-MOTIVIC |
| **Yuan/Arakelov arithmetic volume** | **B**（A=NO；C 当前） | adelic metric/arithmetic volume/positivity 框架 | 新 Arakelov 模型 + detBundle/theta-hull metric 识别；当前无 | FEAS-YUAN |
| **Klein/Siegel/Kronecker** | **A-候选**（条件性 A，当前 B） | Kronecker 极限公式、Klein form、Siegel units 的**显式 arch 公式** + 有限位整性 | theta 乘积 → Klein/Siegel 的 MAPPING；显式不等式形式化 | FEAS-KLEIN / KLEIN-MAPPING |
| **Borcherds 乘积** | **C（直接作 s）；B 仅 X0(N)+Heegner** | 显式 Heegner 除子、权 c(0)/2、无穷乘积 | base→O(2,n) Shimura 映射；Heegner 除子匹配；arch sup≤1；整性 | FEAS-BORCHERDS |
| **Weil/Segal–Bargmann/Hermite** | **A（单 theta sup）；C（乘积/canonical）** | 单 theta Fourier/Mehler 标准 arch 界；Heisenberg 结构 | det 归一化吸收 `−sF·A`；Heisenberg/level 整模型 | FEAS-WEIL-THETA |
| **Tate skeleton/Berkovich** | **A-local（条件）；A-full=NO；B full** | 局部 skeleton `−log|q| = qOrder/(2l)`；`Σj²=nC sF`；Chambert-Loir 测度 | 精确 measure/region 识别；全局 hull 模型 | FEAS-TATE-SKELETON |

## 2. 组合判定

1. **没有任何外部路线当前是 unconditional A**；
2. **最接近 A 的是 Klein/Siegel/Kronecker**：它把 arch 估计换成显式公式，缺的是（标准但需形式化的）theta→Klein/Siegel MAPPING + 显式不等式；
3. **Deligne/Yuan 是 B**：它们把目标重述为 det bundle/arithmetic volume 的截面/度条件，但不提供新的解析或算术下界；
4. **Tropical 的 grouped/error 版是唯一 B 型离散凸路线**，但 exact=C，且需要 actual 全局 submodularity（数值不支持 f_D）；
5. **Borcherds/Weil/Tate 提供局部/显式工具**，但各自有空间、归一化或整性缺口；
6. **Entropy/pluripotential/Brascamp/motivic 对 exact target 是 C**（工具或类比，不是定理）。

## 3. A-local 可用工具清单（可直接用于局部证明/归一化）

### 3.1 Tate skeleton 的 `sF·A_v` 积分/求和
- Tate 参数 `q_v`，`ord(q_v)=qOrder_v`；`A_v=qOrder_v log p_v/(2ℓ)`；
- p-adic theta `θ_q(u)=Σ_n q^{n(n-1)/2}u^n`，零点/准周期显式；
- `qroot` 阶：`ordp_qrootOf = qOrder/(2ℓ·ramIdx)`（GAP-QROOT closed）；
- `Σ_{j=1..nC} j² = nC·sF`，因此 q-side `j²` 权重求和给出 `sF·A_v` 的骨架积分/求和结构；
- 这是 **A-local 候选**：局部 measure/region 精确识别后可严格化。

### 3.2 Weil 单项 arch 界
对标准 theta：
```
|θ(z,τ)| ≤ 1 + 2|q|^{1/2}/(1−|q|),  q=e^{2πiτ}
```
Fourier 绝对收敛 + Mehler/Petersson 给出单 theta 的显式 arch 上界；**A（单 theta）**，但乘积 `∏θ(u_j)^{j²}` 不能由单项界直接 ≤1。

### 3.3 Siegel/Kronecker 显式公式
- Kronecker 极限公式：`E(z,1+ε)=π/ε+4π(γ−log2−log(√y|η(z)|²))+O(ε)`；
- Klein forms：`𝔨_a(z)` 的 theta 商/eta 幂定义 + 变换公式；
- Siegel units 的 arch 范数显式（eta 乘积/Eisenstein 项），有限位整性/生成性标准；
- 这三者是 **A-input（LITERATURE）**；缺 theta 乘积到 Klein/Siegel 乘积的 MAPPING 与显式不等式形式化。

### 3.4 局部 Haar/缩放/Chambert-Loir
- `componentVol(a·O)=−ord(a)logp`/`haar_units_smul`（单映射精确）；
- `componentVol_tensorLogShell_eq`、`leastHull`、`logShellRadius` 局部公式；
- skeleton 上 piecewise affine potential 的 `dd^c` = Chambert-Loir 测度（Tate 局部）；
- 这些是 A-local **B/重述**工具，不是全局下界。

## 4. 外部路线到 A 的最小任务（按优先级）

1. **Klein/Siegel MAPPING**：`∏_j θ(u_j)^{j²} = (∏ Klein/Siegel)·η^M·const`，逐项形式化；
2. **显式 arch 不等式**：由 Kronecker/Siegel 公式证 `arch_bound≤0`；
3. **有限位整性**：Siegel units 整性 + `ordp_qrootOf`/tame 对接；
4. **Tate skeleton 局部积分**：把 `A_v`、`sF`、Chambert-Loir 测度的局部识别写成引理；
5. **Borcherds/Weil**：只作为辅助/归一化工具，不作为独立主路线。

## 5. 结论

**总判定：无 unconditional A；当前最强候选是 Klein/Siegel（A-候选），Deligne/Yuan 为 B，Tate 提供 A-local 工具，Tropical grouped/error 为 B；其余 exact 目标是 C。**
A-local 工具已经足够做局部归一化和显式 arch 计算；真正的缺口仍是 **theta 乘积到 Klein/Siegel 的 MAPPING + 显式不等式 + 有限位整性**，以及 Deligne/Step (xi-d) 的全局 det 比较。

## 文件
- 本文件 `coord/EXTERNAL-FINAL.md`；各路线详见对应的 `coord/FEAS-*.md` / `OUTSIDE-*.md`。