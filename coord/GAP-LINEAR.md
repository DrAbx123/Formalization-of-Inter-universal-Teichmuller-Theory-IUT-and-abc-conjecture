# GAP-LINEAR — 从 paper Step (v) 提取 gap 的 q-线性结构 (A1076)

| field | value |
|---|---|
| Status | **DECISION: Step (v) 只给 rhs/hull 的 UPPER bound（q-线性项 = −sF·A），因此只给 gap 的上界；我们需要的 gap 下界 `(sF−1)A − V` 等价于 Cor 3.12，必须来自 Step (xi-d)，不能从 Step (v) 提取** |
| 源 | `coord/IUT-TEXT-THM110.md` §3-4（IUT IV p.27-29 Step (iv)(v)；pp.22-23 Thm 1.10）；`coord/IUT-TEXT/III.txt:10825-10865`（Step (xi-d)）；`coord/IUT-TEXT-COR312.md`（Cor 3.12） |

## 1. Step (v) 逐句与全部 q-线性项

### 1.1 per-j 上界（p.27-28）
```
(j+1)·log(d^K_{vQ}) − j²/(2l)·log(q_{vQ}) + log(s^Q_{vQ}) + 4(j+1)·l*_mod·log(s^≤_{vQ})
```
q-线性项：**`− j²/(2l) · log(q_{vQ})`**（j 固定）。

### 1.2 j-average（pp.28-29）
```
(l⋆+3)/2·log(d^K_{vQ}) − (2l⋆+1)(l⋆+1)/(12l)·log(q_{vQ}) + log(s^Q_{vQ}) + 2(l⋆+3)·l*_mod·log(s^≤_{vQ})
= (l+5)/4·log(d^K_{vQ}) − (l+1)/24·log(q_{vQ}) + log(s^Q_{vQ}) + (l+5)·l*_mod·log(s^≤_{vQ})
≤ (l+1)/4·{ (1+4/l)log(d^K) − 1/6·log(q) + 4/l·log(s^Q) + 20/3·l*_mod·log(s^≤) }
```
q-线性项（唯一）：**`− (l+1)/24 · log(q_{vQ})`**。

### 1.3 Thm 1.10 结论（pp.22-23）
```
C_Θ = (l+1)/4·|log(q)|·{ (1+12d_mod/l)(log d_Ftpd + log f_Ftpd) + 10(e*_mod·l + η_prm) − 1/6(1−12/l²)·log(q) } − 1
C_Θ ≥ −1  ⇒  1/6·log(q) ≤ (1+20d_mod/l)(log d_F + log f_F) + 20(e*_mod·l + η_prm)
```
q-线性项：`− (1/6)(1−12/l²)·log(q)`（在 C_Θ 括号内，乘 `(l+1)/4|log q|` 后成二次）；
最终 `1/6·log(q) ≤ ...` 是对 `log q` 的**上界**（不是 q 侧下界）。

## 2. 与我们的量对齐

```
A = absLogQ = log(q)/(2l)          （LeftHandSide:81-88）
sF = sFactor nC = l(l+1)/12
(l+1)/24 = sF/(2l)                   （j-average 系数）
⇒ − (l+1)/24·log(q) = − sF·A        （Step (v) 的 q-线性项 = −sF·A）
rhs = −|log Theta|                （我们的 signed 量）
V = logVol(hull vcI)
gap = rhs + sF·A − V              （Gap:521-527）
```
验证 j-average：`(1/nC)Σ_j j²/(2l) = sF/(2l) = (l+1)/24`（nC=(l−1)/2, Σj²/nC=sF）。
最终 `1/6 log q = (l/3)·A`（因 log q = 2l·A）⇒ `(l/3)A ≤ C`，是 **A 的上界**。

## 3. Step (v) 给出 gap 的哪一侧？

Step (v) 是 **hull log-volume 的上界**（IUT IV Step (iv) 明言 "compute an upper bound"）：
```
rhs ≤ P − sF·A,     P := (l+5)/4·log(d^K) + log(s^Q) + (l+5)·l*_mod·log(s^≤)
```
代入 `gap = rhs + sF·A − V`：
```
gap ≤ P − V        （**上界**；q-线性项精确抵消）
```
**我们需要的下界**：variant ⇔ `V + gap ≥ (sF−1)A` ⇔ `gap ≥ (sF−1)A − V`；
这个下界**不在 Step (v)** 中：Step (v) 的 q-线性项（−sF A）与 gap 定义中的 +sF A 完全抵消，
不留下 ∝A 的 gap 项。

## 4. 下界从哪里来

Cor 3.12 结论 `−|logΘ| ≥ −|log q|`（= rhs ≥ −A）直接给出：
```
gap = rhs + sF·A − V ≥ −A + sF·A − V = (sF−1)A − V
```
即 **需要的 gap 下界 ≡ Cor 3.12 本身**；paper 的下界来自 Step (xi-d) 的 determinant 比较
（III.txt:10837-10847："it is only by forming the determinant of the localizations of arithmetic
vector bundles … and then applying the normalized log-volume … that we are able to obtain
completely comparable objects"），不是 Step (v)。

## 5. 条件形式（若将来得到 gap 下界）

若有 `gap ≥ (sF−1)A − (bounded)`（bounded 由 arch/torsion 吸收），则 variant 成立：
```lean
def GapLower (V gap A sF bounded : Real) : Prop :=
  (sF - 1) * A - V - bounded <= gap
theorem variant_of_gap_lower {V gap A sF bounded : Real}
    (h : GapLower V gap A sF bounded) (hb : 0 <= bounded) :
    (sF - 1) * A <= V + gap + bounded :=
  by unfold GapLower at h; linarith
```
但 paper Step (v) 只给上界；下界必须由 Step (xi-d) 提供（GAP-XID）。

## 6. Lean 陈述草案

```lean
/-- j-average coefficient identity: (1/nC)*sum j^2/(2l) = (l+1)/24 = sF/(2l). -/
theorem jAverage_q_coeff (l nC : Nat) (h : nC = (l-1)/2)
    (hsum : (∑ j in Finset.range nC, ((j:Real)+1)^2) = nC * sFactor nC) :
    (1/(nC:Real)) * (∑ j in Finset.range nC, ((j:Real)+1)^2 / (2*(l:Real))) = sFactor nC/(2*(l:Real)) :=
  by rw [← Finset.sum_div, hsum]; field_simp

/-- Step (v) upper-bound form: rhs <= P - sF*A. -/
def StepVUpper (rhs P sF A : Real) : Prop := rhs <= P - sF * A

/-- Gap upper bound from Step (v): gap <= P - V. -/
theorem gap_upper_of_stepV {rhs P sF A V : Real}
    (h : StepVUpper rhs P sF A) : rhs + sF*A - V <= P - V := by
  unfold StepVUpper at h; linarith

/-- Variant from a gap lower bound (conditional). -/
theorem variant_of_gap_lower {V gap A sF bounded : Real}
    (h : (sF-1)*A - V - bounded <= gap) (hb : 0 <= bounded) :
    (sF-1)*A - V <= gap + bounded := by linarith
```

## 7. 结论

1. Step (v) 的全部 q-线性项 = `−j²/(2l)log q`（per j）与 `−(l+1)/24 log q = −sF·A`（平均）；
2. Step (v) 是**上界**：`rhs ≤ P − sF A` ⇒ `gap ≤ P − V`；**不提供** gap 的下界；
3. 我们需要的 `gap ≥ (sF−1)A − V` **等价于 Cor 3.12**（variant），其来源是 Step (xi-d)，
   不是 Step (v)；
4. `1/6 log q = (ℓ/3)A` 的最终不等式是 A 的上界（Szpiro 方向），与 gap 下界无关；
5. 若将来由 Step (xi-d)/determinant 得到 `gap ≥ (sF−1)A − bounded`，则 variant 成立
   （条件语句已给）；bounded 由 arch/torsion 吸收的前提需单独核。