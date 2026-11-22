# C9 completion：E_j 到 source-level C 的 stable reduction、local types 与 C_K/V/ε

任务：task-198（finish E_j into source-level C）。owner：iplsheapt。日期：2026-10-25。stage1 构造/审计；不改 Lean/Project/目标；不引入 arbitrary data；只写本文件。

输入：C9-CONSTRUCT-KCK-20261025.md（task-193，SHA256 E250D5C545AC6F152275B0FC9EC0E4966FF2917318D01B4C684143645C7FD40A）；C9-FULLC-CONSTRUCTION-ATTACK-20261025.md（task-183）；C9-AUDIT-FULLC-CONSTRUCTION-20261025.md（task-184）；IUT I Def3.1(a)-(f)、IUT III Def1.1/Prop1.2/Thm3.11；task-147/149/170/179 纠偏。

状态：stage1 自然语言/精确算术；没有 Lean/Project/kernel/comparator/独立审查；P6 open；target_accepted=false。

## 0. 结果摘要

1. E_j: `j0=1/p^6`，`E_j: y²=x³−3j0/(j0−1728)x−2j0/(j0−1728)`，p=12301。
2. **stable reduction / local types 已算到可构造层**：
   - p=12301：multiplicative I_6，`v_p(Δ)=6`，local q的 valuation6；qhat order b=3；稳定，C_v type `(1,Z/41)^pm`；
   - 2,3：j integral 且 j mod 2,3 不是 0/1728 ⇒ minimal model 在 2,3 good；E_j 的 nonminimal Δ 中的 2,3 因子可消去；
   - D=1−1728p^6 的四个 prime 1009, 50833, 1799579, 64860221162029：j≡1728 mod q，v_q(j−1728)=1，是 potential good additive；semistabilization degree divides 12，primes 2,3；扩展后 good，无 multiplicative q-order；
   - 其他 primes good。所以 `F_sem` 后 bad finite 只剩 p=12301；`V_bad={p}`，q-order b=3 与 41 互素。
3. **F=Q(i,E[6],F_sem)** 的 degree 只含 2,3（E[6] degree≤288；F_sem degree 2,3）；41∤[F:Q]；F/Q Galois；E[2],E[3] rational；K=F(E[41]) 有限 Galois over F。
4. **C_K/C_F/V/ε 的 source-level 构造**：`X_K=E_K\{O}`；`C_K=[X_K/E[41]]` type `(1,41-tors)^pm`；`C_F=[X_F/E[41]]`（F 上 finite group scheme quotient）；K-core `C_F×_F K`；V 是 `V(K)→V_mod` 的 section，选 p 上唯一/一个 place；`ε` 是 origin/canonical cusp。**显式 C_F/C_K/V/ε 方程仍未构造**（见 §5）。
5. **mod41 image 未证明**：E_j 是 non-CM（j 非整、非0/1728）；Serre open image 给 finite index，但 l=41 是否含 `SL2(F41)` 没有 exact computation；IUT I Def3.1(c) 因此仍 conditional/missing。
6. **unit-v dependence**：`qhat=q^{1/82}=π^3 v`，`v∈1+pZ_p`；q=p^6+744p^12+…，v≠1；b=3/order/local type由 v 的 unit 性决定，不依赖 v 的具体值；C_v type 不变。

## 1. E_j 的 exact local data

由 task-193：

```
p=12301;  p^6=3464515518466761109423801;
j0=1/p^6;  E: y²=x³+a x+b,
a=-3/D,  b=-2/D,  D=1−1728p^6
 = −1009·50833·1799579·64860221162029.
Δ=2985984·p^6/D^3;  2985984=2^?3^?.
```

p∤D、2∤D、3∤D（D odd, D≡1 mod3）；`v_p(Δ)=6`，`v_p(j)=−6<0`。

### 1.1 p=12301

- j has v_p=−6；minimal model 是 multiplicative I_6（Tate），q 的 valuation6；
- q 的 Tate expansion：`q=p^6+744p^12+O(p^18)`，故 `q≠p^6`；
- `q/p^6∈1+p^6Z_p`；`p∤82` ⇒ 在 Q_p 中取 82nd root `v`，`qhat=π^3 v`，order b=3；
- `e=41,f=1,p>e+1`；`C_v` 是 type `(1,Z/41)^pm` 的 local quotient；`41∤b=3`，clause (c) 的 q-order 条件在 p 满足。

`π` 在 K_v 中：E[41] 给出 `q^{1/41}`；p≡1 mod41、p∤6，`1+pZ_p` 的41次幂双射，故可解出 `π=p^{1/41}`。K_v/F_p 是 degree41 totally ramified（f=1）。

### 1.2 2,3

D 在 2,3 处是 unit；a,b 在 2,3 整；j0=1/p^6 在 2,3 是 unit；

```
j0 mod 2 = 1 ≠ 0,1728;   j0 mod 3 = 1 ≠ 0,1728.
```

因此 E_j 在 2,3 的 minimal model 是 good；非 minimal Δ 的 2,3 因子可由标准 scaling 消去。没有 bad local type，也没有 q-order。

### 1.3 D primes

对 q∈{1009,50833,1799579,64860221162029}：

```
D≡0 mod q ⇒ 1728p^6≡1 ⇒ j0=p^{−6}≡1728 mod q;
v_q(j0−1728)=1;  j0 integral at q;  q≥1009>3.
```

所以 q 处是 additive potential good；local minimal model 的 Kodaira type 由 j−1728/Δ 的具体 valuations 决定（II/III/IV/I0* 之一），但不论哪一型，q≥5、potential good 的 semistabilization degree divides 12，primes 2,3；扩展后 good，因此没有 multiplicative q-order，也不会成为 V_bad。

精确 local type 的进一步计算（Tate algorithm/最小 discriminant）未做；本文件只使用 potential good/semistabilization 的结论。若需要 explicit C_F local model，需补每 q 的 Kodaira type。

## 2. Stable reduction 与 F_sem

结论：E_j 的 bad finite primes 为 `{2,3,p} ∪ {D primes}`；在 2,3 good，在 D primes potential good additive，在 p multiplicative I_6。取 `F_sem` 为 D primes（必要时 2,3）的 semistabilization compositum；则 `E/F_sem` 只有 p multiplicative，其他 finite good，故 stable reduction over all finite places。

`[F_sem:Q]` 的素因子只来自 2,3（D primes 的 potential good semistabilization degree divides 12；2,3 已 good），因此 41∤[F_sem:Q]。取

```
F := Q(i, E[6], F_sem).
```

E[6] degree divides |GL2(Z/6)|=288；加 i 与 F_sem 后 degree 仍只含 2,3；41∤[F:Q]；F/Q Galois；E[2],E[3] rational；`i∈F`。K=F(E[41]) 是 F 上有限 Galois 扩张。

**条件**：上述 `F_sem` degree 只含2,3 的结论使用标准 potential good semistabilization degree divides12；本文件未逐一执行四个 q 的 Tate algorithm。若某 q 的 semistabilization 需要 degree 含41（不应发生，但未逐项验证），则 F degree 条件需重算。

## 3. K、C_K、C_F、V、ε 的构造

### 3.1 K 与 X_K

```
K=F(E[41]);  X_K=E_K \ {O}.
```

K/F finite Galois；X_K 是 K 上 once-punctured elliptic curve。

### 3.2 C_K 与 C_F

E[41] 是 F 上 finite group scheme（order41²；F char0，étale）。定义

```
C_K := [X_K / E[41]];   C_F := [X_F / E[41]];
K-core(C_K) = C_F ×_F K.
```

C_K 是 type `(1,41-tors)^pm` 的 orbicurve/stack；C_F 的 base change K 得 C_K。显式 coarse equations/stacky points 需要 E[41] 的 41-division coordinates；本文件未给。

### 3.3 V 与 V_bad

F_mod=Q；`V_mod` 是 E 的 bad rational primes；由 §2，E/F 的 bad finite primes 只有 p=12301（其他已 semistabilize good），所以

```
V_mod = {p=12301};   V = choice of the unique/some place of K over p;
V_bad=V,  C_v type (1,Z/41)^pm.
```

V 是 `V(K)→V_mod` 的 section；在 p 处 K_v/F_p degree41 totally ramified，故只有一个 place over p（若 F local 无 residue extension），V 可实际选该 place。

### 3.4 ε

`ε` 取 X_K 的 origin cusp（E 的 zero point去掉后的 puncture）；在 bad v=p 取 canonical generator of Zhat 的 cusp。显式 cusp 坐标需要 E_K/C_K 方程；未给。

## 4. unit-v dependence

p 处 Tate q：

```
q = p^6 u,  u=q/p^6=1+744p^6+O(p^12) ∈1+p^6Z_p;
v := u^{1/82} ∈1+pZ_p  (unique);
qhat = q^{1/82} = π^3 v,   π^41=p.
```

所以：

- `v` 依赖 E_j 的 actual q，不是 arbitrary；
- `v∈1+pZ_p` 是 unit，故 `order(qhat)=3`、`C_v` local type 与 b=3 不依赖 v 的具体值；
- 若强行令 q=p^6（v=1），那是另一个 local normalization，不是 E_j 的 actual q；task-183 的 q=p^6 不能用作 E_j 的 exact value。

## 5. 未完成：mod41 image 与 explicit C

### 5.1 mod41 image

E_j 是 non-CM：j0=1/p^6 是非整 rational，而 CM j 必须是代数整数；且 j≠0,1728。故 Serre open image 给 `Im(G_Q→GL2(F41))` finite index；但 l=41 是否包含 `SL2(F41)` 没有 exact computation。

要完成 clause (c)，必须计算 41-division polynomial 的 Galois group 或 image 的 finite-index subgroup；当前没有该计算。因此：

- `K=F(E[41])` 的 field 本身可用 splitting field 抽象定义；
- 但 `K/F` 的 degree/`[F:Q]` 与 image 是否含 SL2 仍 conditional；
- IUT I Def3.1(c) 未完全验证。

### 5.2 explicit C_F/C_K/V/ε

当前给出 quotient/stack source-level 定义，不给出：

1. E[41] 41-division coordinates/field equations；
2. C_F/C_K coarse equations、stacky points；
3. V 的显式 place choice（p 处唯一性可定，但 global K 的 place 需 field equations）；
4. ε 的 explicit cusp coordinates/canonical generator。

因此 E_j 尚未成为 explicit complete C；只完成 stable reduction/local finite type/q-order 的 source-level 骨架。

## 6. actual / conditional / missing

### 6.1 Actual（条件在标准 Tate/semistabilization 定理）

- E_j/Q actual；j0 rational；p=12301；D factor exact；
- p 处 multiplicative I_6，v_p(Δ)=6，qhat order3；2,3 good；D primes potential good additive；
- F=Q(i,E[6],F_sem) Galois，degree只含2,3，41∤；E[2],E[3],i rational；
- K=F(E[41])，X_K，C_K quotient/type，C_F group-scheme quotient，V section，ε origin/canonical cusp 的 source-level 定义；
- qhat=π³v；v unit；b=3；其他 bad q-order 不存在（semistabilize后 only p）。

### 6.2 Conditional

- 四个 D primes 的具体 Kodaira type/Tate algorithm（本文件只证 potential good）；
- F_sem degree 2,3 的逐项验证；
- mod41 image 含 SL2(F41)；
- K/F degree、F_sem 与 E[6] 的 compatibility；
- V 在 p 处 unique place 的 global field 验证。

### 6.3 Missing

- exact mod41 Galois image（clause c 的关键）；
- explicit 41-division field K、C_F/C_K/V/ε equations；
- complete C 的 BPS/Theta/gluing/target data；
- target/P6。

## 7. 结论

E_j 已经足够给出 **source-level stable local skeleton**：p 处 I_6 与 b=3，D primes potential good additive 可 semistabilize，2,3 good；F_sem 只引入2,3，F degree 41∤；K/C_K/V/ε 有 quotient/formal 构造。**但 mod41 image 和 explicit C equations 未完成**，因此还不是 complete C。task-183 的 q=p^6 已修正为 actual q=p^6+744p^12+…；qhat=π³v、b=3 不依赖 unit v。P6 open。

## 8. 工具/来源

- Python/sympy exact：p primality/congruences、p^6、D factor、Δ formula、q-series；
- IUT I Def3.1(a)-(f)、IUT III Def1.1/Prop1.2/Thm3.11；Tate q-expansion/Silverman Tate algorithm/potential good semistabilization（仅标准结果，未在 Lean 中验证）；
- LMFDB/Cremona web fetch 在本环境被 non-public IP 阻断；未使用外部数据库的曲线数据；没有 arbitrary curve data。
- 本文件只写 md；无 Lean/Project/target edits；target_accepted=false，P6 open。

