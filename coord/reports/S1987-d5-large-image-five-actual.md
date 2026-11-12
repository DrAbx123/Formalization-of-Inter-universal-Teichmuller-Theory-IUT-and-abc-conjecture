# S1987：E'/F' 上 l=5 的 D5 large-image input —— 形式化精确第一 missing，及该命题为真的数学证明

日期：2026-11-01。工作目录 D:/lean。

## 任务与消费者

- 任务：证明 S1982 留下的 `S1982D5ExactFirstMissing = S1894LargeImageInput 5`
  （对 E'[5] 的每个 rank-two 基 b，SL_2(F_5) <= range rho_{5,b}），或给出精确第一 missing。
- 实际消费者：S1982 的 D5 clause `S1982SourceTorsionClause_five`（文件
  tmp/sheaf/xif/paper/S1982D5FiveActual.lean）；以及更上层的
  SerreStyleLargeImageStatement 输入。
- 交付文件：tmp/sheaf/xif/paper/S1987D5LargeImageFiveActual.lean。

## 结论（两句话）

1. **形式化（kernel）状态：MISSING。** 文件 EXIT=0，但其中没有任何
   `S1987D5LargeImageFive` / `S1725ImageContainsSL2 5` / D5 clause 的 inhabitant；
   没有 sorry、axiom、opaque、True/PUnit 或 Nonempty gate。它把该目标与 S1982/S1894
   的等价形式固定下来，并把“精确第一 missing”自身命名。
2. **数学状态：该命题对这条实际曲线为真（非开放）。** 一个人类级证明 + 两组有限
   精确计算（模 13 不可约性、模 29 分解型 (10,2)）给出 mod-5 像在 Q 上就是
   GL_2(F_5)，且 F' 与 5-division field 线性不交，故在 F' 上仍是 GL_2(F_5)，
   从而包含 SL_2(F_5)。该证明尚未形式化；它的缺口是 7 项标准基础设施，见下文。

因此：S1894/S1907 所说“这是开放 Serre 输入”在形式化意义上仍然成立（树中无证明），
但在数学上对 S1667/S1720 这条曲线已经被解决；下游**仍不得**把 target 当已证使用。

## Lean 证据

- 文件：tmp/sheaf/xif/paper/S1987D5LargeImageFiveActual.lean
- 源码 12750 bytes，SHA256 `3397F31D1D7BF355B33C7504ADD915526146FF8ADA9BCC8F450952B34236B691`
- 编译：`lake env lean -j1 -R D:/lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1987D5LargeImageFiveActual.olean ...`，
  **EXIT=0**，无 warning 输出（日志 tmp/s1987/S1987.compile.log，1684 bytes）
- olean 50392 bytes，SHA256 `2887AE61D397ADB44EDCDBD1F0C847DA46A807F77E3248D4EC724F6D0D9E5E55`
- `#print axioms` 覆盖全部 11 个主要声明：仅 `propext, Classical.choice, Quot.sound`
- 禁用项检查：源文件中 `sorry`/`admit`/`native_decide`/`axiom`/`opaque`/`True`/`PUnit`
  只出现在说明性 docstring 里（明确声明“未使用”），代码中没有。

文件证明的正式内容（全部为等价/重述，不含 target 的证明）：

- `S1987D5LargeImageFive`（def）= `S1894LargeImageInput S1987Five`；
  `S1987Five` = `S1982Five`；`S1987D5ExactFirstMissing` 为同一目标的别名。
- `S1987D5LargeImageFive_iff_S1982`：与 `S1982D5ExactFirstMissing` 定义相等。
- `S1987D5LargeImageFive_iff_imageContainsSL2`：与 `S1725ImageContainsSL2 5` 等价。
- `S1987D5LargeImageFive_iff_tail (b)`：**对任意** actual basis b 等价于单基 tail；
  `..._iff_tail_basis` 特指 `S1982Basis`。
- `S1987D5LargeImageFive_iff_serre`：与 `SerreStyleLargeImageStatement S1720Curve 5` 等价。
- `S1987D5LargeImageFive_iff_detKer`：与“每个基下 range 含 det.ker”等价。
- `S1987D5LargeImageFive_iff_S1894ExactMissing`：与 `S1894ExactMissing 5` 等价
  （rank-two 部分已由 S1982 关闭）。
- `S1987D5LargeImageFive_of_fullRange`：单基 range = top 是充分条件（不断言）。
- `S1987SourceTorsionClause` + `_fields` + 四个 field 等式：由目标构造实际 S1725 D5 clause。

## 数学证明（人类级；未形式化）

记号：E = `S1667Curve` : y^2 = x^3 + (61/64) x^2 - (125/64) x = x(x-1)(x+125/64)，
即 Legendre 曲线 lambda = -125/64；E' = E baseChange F'，F' = SplittingField(S1687H*(X^2+1))；
L = Q(E[5])（E 的 5-division field）；G = Gal(L/Q) <= GL_2(F_5)（选 E[5] 的 F_5 基）。

**第 1 步（不可约性 => 12 点传递）。** E 的奇 5-division 多项式 psi_5 次数 12，其根
恰是 24 个非零 5-torsion 点的 12 个 x-坐标（{+-P} 配对）。psi_5 在 Q 上不可约：
其 primitive 整形式（= 2^36 * psi_5，首项系数 2^36*5）模 13 不可约（12 次，squarefree）。
于是 G 在 12 个 pair {+-P} 上的作用传递。

**第 2 步（模 29 给出 (10,2) 型）。** 同一多项式模 29（squarefree；29 不整除
disc(psi_5) = 2^352 * 3^132 * 5^143 * 7^44）分解为一个 2 次不可约因子乘一个 10 次不可约
因子。由 Dedekind 定理，Frobenius(29) 在 12 个 pair 上的轮换型为 (10,2)。

**第 3 步（determinant 满射）。** det G = (Z/5)^*：mod-5 表示的行列式是分圆特征
（Weil pairing：e_5(sP,sQ) = e_5(P,Q)^{det s}，且 e_5 的值生成 mu_5），故
Q(zeta_5) <= L，det G = Gal(Q(zeta_5)/Q) = (Z/5)^*。

**第 4 步（群论：G = GL_2(F_5)）。** 假设 G 真子群。G 含于某个极大子群 M；M 自动
det 满射且 12 点传递。GL_2(F_5) 的极大子群（Dickson 分类）为：
PGL_2(F_5) = S_5 的极大子群（A_5, S_4, F_20, S_3xC_2）的原像，阶 240, 96, 80, 48；
以及可能的 Z 的 complement（阶 120，det 像阶 <= 2，不可能 det 满射）。
逐项精确计算（显式 480 个矩阵、12 个 pair 上的作用）：
- 阶 240（A_5 原像）：det 像 = 平方 {1,4}，非满射；
- 阶 80（Borel = F_20 原像）：12 点不传递（轨道 10 + 2，或 2）；
- 阶 96（S_4 原像）：det 满射、12 点传递，但元素轮换型只有
  id, (2^4,1^4), (2^6), (3^4), (4,4,2,1,1), (4,4,4), (6,6)；
- 阶 48（S_3xC_2 原像）：det 满射、12 点传递，但元素轮换型只有
  id, (2^4,1^4), (2^6), (3^4), (4,4,4), (6,6), (12)；
- GL_2(F_5) 本身另含 (5,5,1,1), (10,2) 两种型。
阶 96 与 48 都不含 (10,2) 型元素，与第 2 步矛盾。故 G = GL_2(F_5)。

**第 5 步（F' 与 L 线性不交）。**
- S1687H 是 6 次不可约多项式，其 Galois 群 6 阶 = S_3，判别式平方类 -3；故
  K := S1687Field = SplittingField S1687H 是 6 次 Galois，二次子域 Q(sqrt(-3))。
- F' = K(i)（H 与 X^2+1 都在 F' 分裂，且 Q(i) 与 K 线性不交：K 唯一二次子域是
  Q(sqrt(-3)) != Q(i)）。故 [F':Q] = 12，Gal(F'/Q) = S_3 x C_2，二次子域为
  Q(sqrt(-3)), Q(i), Q(sqrt(3))（sqrt(3) = -i*sqrt(-3)）。
- L 的二次子域唯一：G = GL_2(F_5) 的 abelianization 是 det: (Z/5)^* = C_4，
  唯一非平凡二次特征为 det^2，其固定域是 Q(zeta_5)^+ = Q(sqrt(5))。
- M := F' cap L 是 Galois 的，Gal(M/Q) 同时是 S_3xC_2 与 GL_2(F_5) 的商；两者
  公共商只有 1 和 C_2（C_2 情形即 Q(sqrt(5))）。Q(sqrt(5)) 不在 F' 的三个二次
  子域中，故 M = Q。
- 于是限制映射 Gal(Qbar/F') -> Gal(L/Q) 满射，F' 上的 mod-5 像 = G = GL_2(F_5)，
  包含 SL_2(F_5)。对任意基（基变换共轭）同样成立，即 target 为真。

## 计算证书（精确、可复跑）

脚本目录 tmp/s1987/，证书日志 tmp/s1987/S1987.certificates.log
（SHA256 `08DFC845811C13E08BFAF6DB699CAA58FFC56E1E733F7E974A35DEB59C0A3EC6`）。

psi_5 的显式构造（脚本 div5.py / verify.py）：

- f = x^3 + (61/64)x^2 - (125/64)x
- psi_3 = 3x^4 + (61/16)x^3 - (375/32)x^2 - 15625/4096
  = (16x-25)(768x^3+2176x^2+400x+625)/4096
- g = 2x^6 + (61/16)x^5 - (625/32)x^4 - (156250/4096)x^2
      - (953125/65536)x + 1953125/131072
- psi_5 = 16 f^2 g - psi_3^3（12 次；首项系数 5）
- 清分母 primitive 形式 P = 2^36 * psi_5（首项系数 2^36*5，内容 1）
- P 在 Q 上不可约；mod 13：单个 12 次不可约因子（squarefree）；mod 29：
  2 次 * 10 次，均不可约（squarefree）；disc(P) = 2^352 * 3^132 * 5^143 * 7^44。

群论证书（脚本 gl25b.py / maxsub2.py / cyc_types.py）：

- GL_2(F_5) 阶 480；(F_5^2\{0})/{+-1} 有 12 个元素。
- 12 点作用下的轮换型分布： (4,4,2,1,1):120, (12):80, (10,2):48, (5,5,1,1):48,
  (6,6):40, (4,4,4):40, (3,3,3,3):40, (2^6):32, (2^4,1^4):30, id:2。
- S_5 = PGL_2(F_5) 的 156 个子群中极大子群阶：60(A_5), 24(S_4)x5, 20(F_20)x6,
  12(S_3xC_2)x10。
- 原像验证：阶 240 det={1,4}、12 点传递；阶 96 det 满射、12 点传递（轮换型见上）；
  阶 80 det 满射、轨道 10 或 2；阶 48 det 满射、12 点传递（轮换型见上）。

脚本 SHA256：div5.py F04577F9..., verify.py EA48F375..., gl25b.py 54A9DB78...,
maxsub2.py F0239D4F..., cyc_types.py 9421B231..., s1687.py BC63A36A...,
factor5.py E421E397...（完整哈希见日志）。

## 精确第一 missing（形式化缺口，按依赖顺序）

target 本身是 `S1987D5LargeImageFive = S1894LargeImageInput 5`；把它变成 kernel 证明需要：

1. **division polynomial 根 <-> 12 个 {+-P} 的 Galois 等变双射**：S1924 的
   group-law criterion（n • P = 0 <-> psi_n(P) = 0）已给出“零点 = torsion”一半，
   但还缺 x-坐标映射的 Galois 等变性、根集与 pair 的基数双射。
2. **Dedekind 分解定理**：p 不整除 disc 时 psi_5 mod p 的因子次数 = Frobenius 在根上的
   轮换型（Mathlib/树中无）。
3. **L = Q(E[5]) 作为有限 Galois 扩域**及 Galois 对应：限制映射满射、固定域、
   M = F' cap L 的计算。
4. **Weil pairing / det = 分圆特征**：e_5 的取值生成 mu_5，Q(zeta_5) <= L。
5. **GL_2(F_5) 的 Dickson 极大子群分类**以及 12 点传递/轮换型的有限计算
   （480 个元素，kernel 可检查，但需要显式枚举或等价手算证明）。
6. **Gal(F'/Q) = S_3 x C_2 及二次子域**：需要 S1687H 的 6 次 Galois 群计算
   （S1687/S1720 已有分裂域、NumberField、IsGalois 实例，但无群结构）。
7. **两个具体多项式证书**（mod 13 不可约、mod 29 分解型）的 proof-producing
   形式化（项目禁用 native_decide，需显式有限域计算证书）。

这 7 项都是标准事实或有限计算，不是新的算术假设；但在它们进入 kernel 之前，
target 在 Lean 中保持 MISSING。

## 树内数据为何不能推出（负结果）

- S1708“九点单射”是条件 (b) 的 3-torsion 计数 Nat.card E[3] = 9
  （六个 3-torsion y-坐标 + P + (-P)），与 mod-5 像无关。
- S1720/S1725 的 split multiplicative reduction（place 7）、奇剩余 7、mu_6 carrier
  只给局部/行列式数据；树中没有 Tate uniformization、inertia 作用或 Weil pairing
  接口，不能把它们变成 mod-5 矩阵元素。
- 全树 grep：`S1725ImageContainsSL2`、`S1894LargeImageInput`、
  `SerreStyleLargeImageStatement` 没有任何证明结论，只有定义、假设与等价。
- 因此 S1894 的“exact first missing”结论作为形式化状态仍然有效；本文件没有 fake。

## 对既有记录的修正说明

- 本结果修正的是**数学状态**而非**形式化状态**：S1894/S1907 记录的
  “no available arithmetic inputs yields the image statement”仍适用于已形式化数据；
  但对 S1667/S1720 这条具体曲线，mod-5 像可以完全确定（= GL_2(F_5)），
  所以该 large-image 输入不是不可及的开放猜想，而是一个可完成的有限验证 + Galois 桥。
- 不影响任何下游使用：在 7 项缺口形式化之前，`S1982D5ExactFirstMissing` 仍必须作为
  假设使用，不得作为定理。

## 下一步（可执行）

1. 若项目决定关闭此节点：新建 DAG 节点 “l=5 division-field/Galois bridge”，
   先做 (5)(6) 的有限群/6 次 Galois 群计算（不依赖 Dedekind），再做 (1)(2)(3)(4)；
   (7) 最后以显式有限域证书完成。
2. 若暂不投入：保留本文件为 missing endpoint；S1982 链在单个显式输入下已闭合，
   消费者不变。
3. 任何“证明”都不得用新增 axiom/opaque/native_decide 替换上述 7 项。

## 证据边界

- 计算证书用 Python/sympy 精确有理/整数运算复跑（非 Lean kernel 检查）。
- 人类证明使用标准定理（Dedekind、Dickson、Weil pairing、Galois 对应），未形式化。
- Lean 文件只证明等价与接口；target 未证。EXIT=0 不等于 target 已闭合。
