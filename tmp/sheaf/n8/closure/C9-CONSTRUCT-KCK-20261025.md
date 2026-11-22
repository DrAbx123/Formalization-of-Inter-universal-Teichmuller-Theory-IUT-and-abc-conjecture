# C9 构造：从实际 E 构造 K、C_K、V、ε

任务：task-193（Construct K, CK, V, epsilon from actual E）。owner：iplsheapt。日期：2026-10-25。stage1 构造/审计；不改 Lean/Project/目标；不引入 arbitrary data；只写本文件。

输入：C9-FULLC-CONSTRUCTION-ATTACK-20261025.md（task-183）；C9-AUDIT-FULLC-CONSTRUCTION-20261025.md（task-184）；IUT I Definition 3.1(a)-(f)（May 2020, pp.61-64）；IUT III Def1.1/Prop1.2/Thm3.11；已冻结 C9 纠偏（task-147/149/170/179）。

状态：没有 Lean/Project/kernel/comparator/独立审查；P6 open；target_accepted=false。

## 0. 结果摘要

1. **实际候选 E 已构造**：取 p=12301，`j0=1/p^6`，

   `E_j: y² = x³ − 3j0/(j0−1728) x − 2j0/(j0−1728)`. 这是 Q 上实际椭圆曲线，j(E_j)=j0∈Q；p 处有乘法 reduction，`v_p(Δ)=6`（见 §1）。
2. **F=Q(i,E[6]) 的 degree 对 41 素数无关**：E[6] 的 Galois 群是 GL2(Z/6) 的子群，`#GL2(Z/6)=288`；加上 i 的二次扩张，`[F:Q] | 2·288=576`，只含素因子 2,3，故 41∤[F:Q]；F/Q Galois，E[2],E[3] 全 rational，`i∈F`。**K=F(E[41])** 是 F 上的有限 Galois 扩张。
3. **C_K、X_K、V、ε 有形式构造**：`X_K=E_K\{O}`；`C_K=[X_K/E[41]]` 是 type `(1,41-tors)^pm`；K-core 为 `C_F×_F K`；V 是 bad places 的 section，ε 是由 origin/canonical cusp 给出的 cusp。**显式 C_F/C_K/V/ε 方程仍缺**；K 的 explicit field equations/degree/mod-41 image 未构造。
4. **task-183 的 `q=p^6`/j rationality 已核**：j0 的 rationality 是 actual（E_j 定义在 Q）；但 E_j 的 local Tate q **不是** p^6：由 j(q)=q^{−1}+744+196884q+… 的反演，

   `q = p^6 + 744 p^12 + O(p^18) ≠ p^6`。

   所以 task-183 把 j=Tate j(p^6) 当作 rational、并直接写 q=p^6 的两步不成立。**但** local q 仍满足 `v_p(q)=6`，且 `q/p^6 ∈ 1+p^6Z_p ⊂ 1+pZ_p`；p∤82，`x↦x^82` 在 `1+pZ_p` 上双射，故 q 在 Q_p 中有 82-th root；K 的 local field 包含 π=p^{1/41}，于是 `qhat=q^{1/82}=π^3·v`（v∈1+pZ_p），order b=3 仍实际成立。这是比 task-183 更精确的 local 结论。
5. **未完成的 clause 验证**：E_j 的 stable reduction over F（2,3 与 D 的 primes）、其他 bad places 的 q orders、mod-41 image 含 SL2(F41)、C_F/C_K explicit、V/ε actual cusp；这些 missing，不是已构造。

## 1. 实际 E_j 与 p 处 local type

取 p=12301。Python exact checks：

```
p prime = True
p mod 41 = 1; p mod 6 = 1; p mod 4 = 1;
p^6 = 3464515518466761109423801;
j0 = 1/p^6;
E_j: y² = x³ − 3j0/(j0−1728) x − 2j0/(j0−1728);
Δ(E_j) = 2985984·j0²/(j0−1728)³
       = 2985984·p^6/(1−1728p^6)^3;
D := 1−1728p^6 = −1009·50833·1799579·64860221162029.
```

因此 `v_p(Δ)=6`（D 不被 p 整除），`v_p(j0)=−6<0`：在 Q_p 上 E_j 有 multiplicative reduction（Tate）；local q 的 valuation 为 6。

### 1.1 q 与 qhat 的精确关系

标准 Tate q-expansion：

```
j(q) = q^{−1} + 744 + 196884 q + 21493760 q² + …
```

反演 x=1/j：

```
q = x + 744 x² + 750420 x³ + O(x⁴).
```

代 x=1/j0=p^6：

```
q = p^6 + 744 p^12 + O(p^18) ≠ p^6.
```

所以 task-183 的 `q=p^6` 对 rational j 不成立；rational j 只保证 v_p(q)=−v_p(j)=6，不保证 q 的有理值。

**qhat order 3 的修正证明：**

`q/p^6 = 1 + 744 p^6 + O(p^12) ∈ 1+p^6Z_p ⊂ 1+pZ_p`。p=12301∤82，`x↦x^82` 是 pro-p group `1+pZ_p` 的自同构；故存在 `v∈1+pZ_p` 使 `v^82=q/p^6`。令 `π^41=p`，则

```
qhat := q^{1/82} = π^3 · v,   v∈1+pZ_p;
qhat^82=q,   order(qhat)=3 (in K_v).
```

这里 π 在 K=F(E[41]) 的 local field 中：E[41] 的 Tate 点给出 q^{1/41}，而 p≡1 mod41、p∤6、`1+pZ_p` 的41次幂双射，故可解出 π（gcd(6,41)=1）；local e=41,f=1。

## 2. F、K 与 field-of-moduli

取

```
F_mod = Q;   F = Q(i, E[6]);   K = F(E[41]).
```

实际性：

- E_j/Q 的 j∈Q，故 field of moduli F_mod=Q；
- E[6] 在 F 上全 rational（by definition），特别 E[2],E[3] 全 rational；
- i∈F，满足 IUT I Def3.1(a)；
- F/Q 是 Galois（E[6] 的 splitting field 与 Q(i) 的 compositum）；
- `[F:Q] | 2·|GL2(Z/6)| = 2·288=576`，故 41∤[F:Q]；
- K/F 是有限 Galois（E[41] 的 splitting field）。

**缺失**：K 的 explicit field equations、`[K:F]` 的实际值、mod41 image 是否含 `SL2(F41)`。若 image 不含 SL2，则 IUT I Def3.1(c) 失败；E_j 是 generic non-CM 曲线，但这需要实际计算，不能由 field degree 推出。

## 3. X_K、C_K、K-core、ε

由 E_K：

```
X_K := E_K \ {O};
C_K := [X_K / E[41]]     (quotient orbicurve/stack);
type(C_K) = (1, 41-tors)^pm.
```

K-core：`C_F ×_F K`，其中 `C_F` 是 E[41] 作为 F 上有限 group scheme 的 quotient 的 F-form；K-core 的 coarse moduli 是 `X_F`，`C_K→C_F` 由 base change K/F 给出。

`ε`：取 `X_K` 的 cusp（origin O 去掉后的 puncture）作为 `ε`；在 bad v 处取 canonical generator of Zhat 给出的 cusp。具体坐标/局部 uniformizer 需显式 E_j 方程与 C_F/C_K 方程；本文件只给出 source-level 构造。

## 4. V、V_bad 与 local type

F_mod=Q 时，`V_mod=V(F_mod)` 是 E_j 的 bad rational primes 的集合。由 §1：

```
p=12301 ∈ V_bad_mod;
2,3 ∈ V_bad_mod (Δ 分子 2985984=2^?3^?);
D 的四个 prime 1009, 50833, 1799579, 64860221162029 ∈ bad;
其他好的 rational primes 不在 V_mod.
```

V 是自然 map `V(K)→V_mod` 的一个 section；对每个 rational bad p，choose one place of K over p。V_bad=V∩V(K)_bad。

在 p=12301：local field K_v/F_p 的 e=41,f=1，qhat order b=3，p>e+1；`C_v` type `(1,Z/41Z)^pm` 由 E[41] quotient 给出；`41∤b` 满足 q-order 条件。

其他 bad primes：E_j 在 2,3 处可能 additive，在 D primes 处 potential good/additive；其 local q/order 和 `41∤order` 未计算。若某个 bad q 的 q-order 被41整除，IUT I Def3.1(c) 失败；需 twist/选择不同 j。

## 5. task-183 的 q=p^6 / j rationality 结论

| 断言 | 本文件结论 |
|---|---|
| j 可 rational | **Verified actual**: E_j with j0=1/p^6 ∈ Q |
| q_Tate=p^6 | **False in general**; E_j gives q=p^6+744p^12+…≠p^6 |
| qhat=π^3, b=3 | **Actual at p** via 82nd power correction, not via q=p^6 |
| global E stable at all bad places | **Missing/conditional** |
| mod41 image contains SL2 | **Missing/conditional** |
| full K/C_K/V/ε explicit | **Missing**; formal construction only |

因此 task-183 的 `q=p^6` 是 local candidate 的 normalization，不是 rational j 的自动结果；本文件把它替换为 exact Tate q 的 valuation/约化论证，并保留 b=3 的实际性。

## 6. actual / conditional / missing

### 6.1 Actual

- p=12301 prime, p≡1 mod41, p≡1 mod6/4; `p^6` exact;
- E_j/Q actual equation/rational j; `v_p(Δ)=6`, `v_p(j)=−6`;
- local q=q(p^6) expansion and `q≠p^6`; q/p^6∈1+pZ_p;
- qhat existence/order3 via 82nd power map; local e=41,f=1;
- F=Q(i,E[6]) Galois degree divides576, 41∤; E[2],E[3] rational; K=F(E[41]) formal actual;
- X_K, C_K quotient type, V section existence, ε origin/canonical cusp formal.

### 6.2 Conditional

- stable reduction of E_j over all bad places of F (semistabilization extension degree prime to41);
- E[41] mod image contains SL2(F41);
- other bad q-orders 41∤;
- explicit C_F/C_K/V/ε equations/coordinates;
- field of moduli/actual K equations.

### 6.3 Missing

- actual complete C with all clauses;
- explicit E/F/clauses; field F semistabilization;
- actual V places/canonical cusp coordinates;
- explicit C_F/C_K;
- q=p^6 exact (false for E_j);
- target/Theta/BPS data; P6 global.

## 7. 工具与来源

- Python 3.14/sympy exact: primality, congruence, p^6, Δ factor, q-series reversion. Web/LMFDB/Cremona fetch was blocked: hostname resolves to non-public IP in this environment; no external database value used. IUT I Def3.1(a)-(f) and Tate q-expansion are the only math sources; no arbitrary curve data.
- IUT I May 2020 Def3.1(a)-(f) pp.61-64; IUT III Def1.1/Prop1.2/Thm3.11; E_j standard j-line model; Tate uniformization.</ br>
- No Lean/Project edits; only this file written.

## 8. 结论

从实际 E_j 可以写出 K=F(E[41])、X_K、C_K、V section、ε cusp 的 source-level 构造；但 full IUT I Def3.1(d)(e)(f) 的 explicit C_K/V/ε 仍缺，且 E_j 的 stable reduction、mod41 image、其他 bad q-orders 未验证。故当前是 **partial actual + conditional skeleton**；不是完整 C，也不是 P6 证明。task-183 的 q=p^6 假设已核为 false（rational j 不强制 q=p^6），但 local b=3 通过 exact q order/82nd power 修正仍成立。

