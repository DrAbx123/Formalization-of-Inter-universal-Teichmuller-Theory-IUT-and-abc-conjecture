# C9：E_j 的 per-D Kodaira types 与 F_sem degree

任务：task-206（Exact per-D Kodaira types and F_sem degree）。owner：iplsheapt。日期：2026-10-25。stage1 精确局部算术/构造；不改 Lean/Project/目标；不依赖 LMFDB；不引入 arbitrary data；只写本文件。

输入：C9-EJ-COMPLETION-20261025.md（task-198，SHA256 08F308CD1F656520BE3668B0C62776BA8CD38AFB66A34C7BD5522696BC7EA226）；C9-AUDIT-EJ-20261025.md（task-199）；C9-CONSTRUCT-KCK-20261025.md（task-193，SHA256 E250D5C545AC6F152275B0FC9EC0E4966FF2917318D01B4C684143645C7FD40A）；IUT I Def3.1；Tate algorithm/Kodaira 分类的 standard tables（不依赖数据库）。

状态：没有 Lean/Project/kernel/comparator/独立审查；P6 open；target_accepted=false。

## 0. 结果摘要

1. `D=1−1728p^6=−1009·50833·1799579·64860221162029`，squarefree。对每个 q|D，精确 Kodaira type 是 **III***：最小模型的 `(v(c4),v(c6),v(Δ))=(3,5,9)`。
2. 每个 q|D 的 local semistabilization degree 是 **4**（quartic ramified extension `q^{1/4}` 后 good；e=1,2,3 不足）。
3. D-part 的 `F_sem` 每 q 的 local degree4；global D-part degree 是 2-power，且 ≤4·4·4·8=512（三个 q≡1 mod4 quartic cyclic，q=1799579≡3 mod4 Galois closure degree8；共同含 Q(i)，故实际 degree ≤512）。**exact global degree 未由本文件确定**，但只含素因子2，41∤。
4. 2,3 处 E_j 是 bad additive（不是 task-198 原先的 good）：p=2 的 reduction singular，p=3 的 reduction singular；其精确 Kodaira type/local semistabilization degree 在本文件未算，但 p=2,3 的 semistabilization degree 只含2,3，41∤。
5. 因此 `F_sem`（D-part + 2,3 factors）degree 只含2,3，41∤；D-part exact local type/degree 已算；exact total global degree 仍 missing。
6. 在 F_sem 后 D-primes 与 2,3 变 good，p=12301 仍是 multiplicative I_6；V_bad 只剩 p；其他 bad q-order 不存在；p 的 qhat order b=3 与 v 单位无关。

## 1. D primes 与 local model

E_j: `y²=x³+a x+b`，`a=-3/D`，`b=-2/D`，`D=1−1728p^6`。

```
p=12301;  D=−1009·50833·1799579·64860221162029;
each q|D: q≥1009, q∤2985984, q∤p, D=qD', q∤D'.
```

在 q 处 v_q(a)=v_q(b)=−1，v_q(Δ)=−3（nonminimal model）。取 `u=q^{−1}` 的 scaling

```
x=u²X, y=u³Y  ⇒ a'=a u^{−4}=a q⁴, b'=b q⁶, Δ'=Δ q^{12}.
```

得到 integral minimal model：

```
v_q(a')=3,  v_q(b')=5,  v_q(Δ')=9;
v_q(c4')=v_q(−48a')=3,  v_q(c6')=v_q(−864b')=5.
```

在 p≥5 的 Kodaira/Tate table 中，`(v(c4),v(c6),v(Δ))=(3,5,9)` 唯一对应 **type III***（不是 I3*；I3* 的 c4,c6 valuations 更高）。故每个 D prime 精确 type = III*。

## 2. Local semistabilization degree = 4

在 q 处取 ramified extension K'=Q_q(π') with `π'^4=q`。最小 model 的 a',b' 是 `q³ a0, q⁵ b0`（a0,b0 units），在 K' 中 `q=π'^4`，故

```
a'=π'^{12}a0,  b'=π'^{20}b0,  Δ'=π'^{36}Δ0 (Δ0 unit).
```

取进一步 scaling `u=π'^3`（x=u²X,y=u³Y）：

```
a''=a'/u⁴=π'^{12−12}a0 unit;
b''=b'/u⁶=π'^{20−18}b0=π'^2 b0;
Δ''=Δ'/u^{12}=π'^{36−36}Δ0 unit.
```

Δ'' 是 unit，故在 K' 上 E 有 good reduction。e=1,2,3 时，minimal scaling 后 Δ 的 valuation 分别为9,6,3（normalized），都不能降到0；所以最小 semistabilization degree 是 **4**。

四个 D primes 的 local degree 都是4，故 D-part 的 semistabilization 每 q 是 quartic/其 Galois closure。

## 3. Global F_sem D-part degree

D primes: 1009,50833,1799579,64860221162029；mod4：1,1,3,1。

```
q≡1 mod4: q^{1/4} quartic cyclic over Q_q (μ4⊂Q_q); Galois degree4;
q=1799579≡3 mod4: x^4−q Eisenstein; Galois closure degree8 (includes i);
all D local fields contain Q(i); D-part compositum degree ≤4·4·4·8=512 = 2^9.
```

因此 `[F_sem^D:Q]` 只含2，且 ≤512；若需 exact degree，需要计算四个 local fields 的交（它们至少共同含 Q(i)，所以不是简单4⁴；本文件不伪造 exact value）。D-part 不含41。

## 4. 2,3 处：bad additive，不是 good

Task-198 原先把 2,3 判为 good；本文件修正：

- q=2：a=-3/D 是2-adic unit，b=-2/D 的 v2=1；Δ 的 v2=12（2985984=2^12·3^6）。reduce mod2：`y²=x³+x`（b≡0,a≡1）在 F2 是 singular；故 bad additive，不是 good。
- q=3：a 的 v3=1，b 是3-adic unit；Δ 的 v3=6。reduce mod3：`y²=x³+1` 在 F3 singular（x³+1=(x+1)³）；故 bad additive。

精确 Kodaira types/local semistabilization degrees at 2,3 需要 char2/3 的 Tate algorithm；本文件未算。但 p=2,3 的 semistabilization degree 只含2,3（wild 2,3 的 finite constant），不会引入41。

## 5. F_sem 与 bad set

取 `F_sem` 为 D primes quartics（及其 Galois closure）与 2,3 semistabilization 的 compositum。则：

```
[F_sem:Q] 的素因子只来自 2,3;  41∤[F_sem:Q];
D primes 与 2,3 在 F_sem 后 good;
p=12301 仍 multiplicative I_6;  V_bad={p}.
```

故 other bad local types/q-orders：D primes 没有 multiplicative q-order（semistabilize 后 good），2,3 也没有；只有 p 的 qhat order b=3。`F=Q(i,E[6],F_sem)` degree 只含2,3，41∤。

## 6. exact F_sem degree 的状态

**Exact local degree:** 每个 D prime =4；p 处=1；2,3 处 exact unknown but 2,3-smooth。

**Global exact degree:** 本文件只给 D-part `≤2^9=512` 且 2-power；加上2,3后总 degree 仍是 2,3-smooth。要得到 exact `[F_sem:Q]`，需：

1. 显式写每个 q 的 quartic/ Galois closure（本文件只做 valuation scaling）；
2. 计算四个 local fields 的交（都含 Q(i)，需要具体 field compositum）；
3. 2,3 的 Kodaira type/local degree；
4. 这些 field 的线性无关性。

因此 task 的 “exact per-D Kodaira types” 已完成（III*）， “local F_sem degree” 已完成（4 each）；**global exact F_sem degree 仍 conditional/missing**，但 41∤ 是确定的。

## 7. actual / conditional / missing

### Actual / exact

- D factor exact; each q|D type III* with (v(c4),v(c6),vΔ)=(3,5,9);
- each D q local semistabilization degree4; exact scaling proof;
- D-part global degree ≤512, 2-power;
- 2,3 bad additive (exact types not computed);
- p type I6; qhat order3; no other q-orders after F_sem; V_bad={p};
- F_sem total degree 2,3-smooth; 41∤.

### Conditional

- exact global F_sem degree (need intersections/local fields);
- 2,3 exact Kodaira types/degrees;
- existence of global Galois semistabilization fields with only D/2,3 ramification;
- explicit C_F/C_K/V/ε, mod41 image (still missing from task-198).

### Missing

- exact 2,3 Kodaira types; exact global F_sem degree;
- explicit local/global field equations;
- mod41 image SL2; and all downstream C9 target data.

## 8. 结论

Per-D 精确结果是：四个 D primes 全部 **III***，local semistabilization degree 4；D-part global degree ≤512=2^9，无41。2,3 实际是 bad additive（修正 task-198 的 good 断言），但其 exact local types/degrees 未算；它们只贡献2,3，不影响 41∤。F_sem 后只有 p=12301 bad multiplicative I_6，qhat order b=3；因此 other bad q-orders 不存在。Task 的 exact per-D Kodaira type 与 local F_sem degree 完成；exact global F_sem degree 与 explicit C/mod41 仍 missing。P6 open。

## 9. 工具/来源

- Python/sympy exact：D factorization、mod4 residues、valuation/scaling、2985984=2^12·3^6；
- Kodaira/Tate 分类表（standard，p≥5）；semistabilization scaling 直接计算；
- 无 LMFDB/Cremona 数据；无 arbitrary curve data；
- 只写本 md；无 Lean/Project/target edits；target_accepted=false，P6 open。

