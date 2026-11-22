# C9 new-math program：global height / Faltings interpretation of Q_C and h_C

任务：task-246（global height/Faltings interpretation）。owner：iplsheapt。日期：2026-10-25。自然语言 new-math 探索；不改 Lean/Project/目标；不设 arbitrary heights；只写本文件。

背景：Kondo H_A/B 与 TC-A..H/TC-S 仍未闭合。尝试把 `Q_C`、`h_C` 解释成显式线丛/cycle 的 arithmetic height/Arakelov degree，用 positivity/ampleness 绕过 TC；并用 b=3 finite deficit 与 arch bound 做检验。

状态：没有 Lean/Project/kernel/comparator/独立审查；P6 open；target_accepted=false。

## 0. Verdict

1. 存在一个**形式化 dictionary**：

```
Q_C = deg_Ar(L_Q),      h_C = deg_Ar(L_Θ),
Q_C ≤ h_C  ⇔  deg_Ar(L_Θ ⊗ L_Q^{−1}) ≥ 0.
```

这可以把 target inequality 改写成 arithmetic line bundle 的 positivity question，形式上 bypass Kondo/TC。
2. **但没有得到无条件 height inequality。** positivity/ampleness 需要额外的 effective/nef/Green-function 条件；当前 C9 数据没有这些条件。
3. **b=3 B=O_K test 直接否定**“current h_C/Q_C 上的 naive positivity”：

```
Q_C−h_C|b=3,B=O_K = (408/41)log 12301 = 93.7149712746… natural;
h_inf ≤ (l+5)/4 logπ = 13.1643936873… natural;
gap ≥ 80.5505775873… > 0.
```

所以若把 `L_Θ` 认作 current h_C、`L_Q` 认作 current Q_C，则 `L_Θ⊗L_Q^{−1}` 的 arithmetic degree 在 b=3 B=O_K profile 上是负的；任何“current line bundle is nef/effective”式的 positivity theorem 都会在这里失败。
4. B=I 条件分支可以给 surplus（h−Q=12/41 logp=2.7563）且 arch 可补，但 B=I 未 actual；b=273 即使 B=I 仍巨负。因此 height route 至多给 conditional branch inequality，不能替代 TC/actual B。
5. **Impossible from current data**：若 height 只使用 current local h/Q 数据，Q_C≤h_C 在 b=3 B=O_K 上为假；要救它必须加入一个未定义的正 height 项（新 cycle/auxiliary Faltings height），那已不是当前 h_C，属新的 arbitrary input。

## 1. Candidate dictionary

固定 F/Q 与 bad set S；p∈S，q-parameter order b_p，ramification e_p。current C9 的有限量是

```
Q_C = Σ_p Q_p = −Σ_p (b_p/e_p) log p;
h_C = Σ_p h_p + h_inf(C).
```

定义 Hermitian line bundles on Spec O_F（或 on the relevant arithmetic curve/stack）：

```
L_Q := O(−D_Q) with D_Q = Σ_p (b_p/e_p)[p] and the canonical log metric;
L_Θ := the theta-pilot line bundle with the metric whose local log-volume
        is h_p at p and h_inf at archimedean places.
```

则 (formal, conditional on the existence of these Hermitian metrics)

```
deg_Ar(L_Q)=Q_C,   deg_Ar(L_Θ)=h_C.
```

注意：这不是把 `Q_C/h_C` 强行贴到任意 height；`L_Q` 的 divisor 来自 q-order，`L_Θ` 的 metric 来自 theta-pilot/l hull。但 source 未证明 `L_Θ` 是 Faltings/theta line bundle 的 standard metric；这一步是 **conditional dictionary**。

## 2. Faltings/theta candidates

### 2.1 Faltings height

Faltings height 的 local form（standard，示意）

```
h_F(E) = (1/[F:Q]) ( log vol(H^0(Ω)^*) + Σ_p local terms + arch terms ).
```

在 bad multiplicative p 处，`−log|q_p|` 型项与 `Q_p=−(b_p/e_p)logp` 同量纲；在 good places 无 q 项；arch 项给 height 的 Green function。于是可尝试

```
Q_C = −h_F(E) + (good/auxiliary terms),   h_C = h_Ar(Θ-pilot cycle)
```

但 Faltings height 是 elliptic curve/abelian variety 的 height，不是任意 hull 的 volume；`h_C` 是 procession-normalized log-volume。两者之间的 identification 需要：

```
HF1. 一个显式 E/F 或 theta divisor D_Θ，使 h_C = deg_Ar(D_Θ);
HF2. Q_C = −deg_Ar(Hodge/theta line bundle) up to an explicit local factor;
HF3. metric/Green function normalization 与 C9 的 B_I/shell-pi convention 一致.
```

当前 source 没有 HF1-HF3。

### 2.2 Bost-Zhang / Bost-Connes positivity

Bost-Zhang arithmetic Hilbert-Samuel 给 `h^0(L^n)` 的 asymptotic degree；Bost-Connes 给 height/state 的 positivity formalism。它们能提供“若 L 有足够多 small sections 则 deg≥0/≥lower bound”的定理，但不能从 arbitrary line bundle 得到 pointwise `Q_C≤h_C`。需要：

```
POS1. L_diff=L_Θ⊗L_Q^{−1} is effective/nef/big with controlled metric;
POS2. a nonzero section/cycle with sup norm ≤1;
POS3. the theta divisor is actually a divisor of the metric, not an arbitrary cycle.
```

即使用 Bost-Zhang，POS1-3 也是额外 source/target 条件，不自动满足。

## 3. Positivity implication (conditional)

**Proposition H-Pos (conditional).** 若 `L_diff=L_Θ⊗L_Q^{−1}` 有一个 nonzero global section s，且其 metric 满足 `sup |s|≤1`，并且 `L_diff` 的 arithmetic degree 由该 effective section 的 divisor 控制（standard arithmetic effectivity），则

```
deg_Ar(L_diff) ≥ 0,   hence Q_C ≤ h_C.
```

这是标准的算术 effectivity/positivity 方向；不是新定理。它没有说明 current `L_diff` 满足 POS1-3。

对 target 的更现实版本是带 arch/auxiliary correction 的

```
Q_C ≤ h_C + A_extra,     A_extra = archimedean/Green/theta correction;
```

此时必须把 `A_extra` 作为 explicit line bundle/Green function 的一部分计算；不能把任意大的 auxiliary height 塞进 `A_extra`（那会违反 no arbitrary heights）。

## 4. b=3 finite deficit test

取 F=Q、单 bad p=12301、e=41、b=3。current local formulas：

```
B=O_K:  Q_p=−3/41 logp,  h_p=−411/41 logp;
B=I:    Q_p=−3/41 logp,  h_p=9/41 logp.
```

因此

```
B=O_K: Q_p−h_p = (408/41)logp = 93.7149712746… natural;
B=I:   h_p−Q_p = (12/41)logp  = 2.7563226845… natural.
```

arch max（current source container bound）

```
h_inf ≤ 11.5 logπ = 13.1643936873… natural.
```

B=O_K：`h_C−Q_C ≤ 13.16439−93.71497 = −80.55058 <0`。所以 current `h_C` 在 b=3 B=O_K 上不满足 height inequality；这正是 §0 的 obstruction。B=I：`h_C−Q_C ≤ 2.75632+13.16439 = 15.92072 >0`，但 B=I 只是 conditional，且不是 actual under natural trace alignment。

b=273 test（B=O_K residual 38883/41；B=I residual 38463/41）：

```
B=O_K: Q−h = (38883/41)log12301 = 8931.17457860…;
B=I:   Q−h = (38463/41)log12301 = 8834.703284644…;  both ≫ arch 13.164.
```

故即使 B=I，b=273 的 height inequality 也失败；height positivity 不能对所有 b 成立。

## 5. What the test proves / does not prove

**Exact conditional arithmetic**: under current local b=3 B=O_K formulas and current arch bound, `Q_C>h_C`; thus no positivity theorem for the **current line bundle dictionary** can hold. Under B=I, `h_C>Q_C` locally, but B=I is not actual and arch corrections are conditional. The test is not a global counterexample to the original target because the actual C/branch is not constructed; it is a **falsification of the proposed height route as stated**. 

**No arbitrary escape**: adding an auxiliary Faltings height `h_F(E_aux)` or an arbitrary effective cycle to `L_Θ` can make the inequality true, but then the object is no longer the C9 `h_C`. Any such addition must be derived from the source Theta-pilot/Faltings line bundle; it cannot be chosen to fit b=3.

## 6. Could a genuine height theorem beat the obstruction?

For a genuine Faltings/theta height, there are possible positive terms not in current `h_C`:

1. **Hodge bundle degree / Faltings height of an auxiliary abelian variety**: can be positive and large; but no source identification with h_C;
2. **theta divisor self-intersection / Hodge index**: gives a quadratic positivity, not a linear lower bound for a point;
3. **archimedean Green functions**: current h_inf bound is 13.164, but a different metric/normalization could produce a different arch term; IV B_I/shell-pi normalization conflict means this is not free;
4. **global Faltings height** of an actual elliptic curve E/F: can be positive or negative; no universal lower bound enough for b=273 (residual 8931) without source height growth;
5. **Bost-Zhang effective section**: if L_diff has a section, its degree is controlled by zeros at finite places; the b=3 negative degree would require zeros/positive divisor at other places, which must be exhibited.

So a valid height proof would have to construct a **specific extra effective divisor/line bundle** with arithmetic degree at least +80.55 natural for b=3 and +8918 for b=273, and identify it with the C9 target. None exists in current data. This is the exact missing object, not a generic positivity theorem.

## 7. A conditional height theorem (usable statement)

**Theorem H-F (conditional).** 设

```
(i)  Q_C=deg_Ar(L_Q), h_C=deg_Ar(L_Θ) for explicit Hermitian line bundles
     L_Q,L_Θ whose metrics come from the q-pilot/Theta-pilot source data;
(ii) L_diff=L_Θ⊗L_Q^{−1} is effective/nef with a nonzero section of
     sup norm≤1, or has an explicit effective divisor D with
     deg_Ar(L_diff)=deg_Ar(D)+Green ≥0;
(iii) the line-bundle identification is compatible with the target column,
     row/place, Theta-gluing and normalization.
```

则 `Q_C≤h_C`. 证明即 arithmetic effectivity/degree additivity。这个定理不依赖 Kondo H_A/B 或 TC，但它的 hypothesis (i)-(iii) 恰好是当前缺失的 source/target height dictionary；没有它们，定理为空。

H-F 的 b=3 检验：current `L_diff` 在 B=O_K 上 degree 为负，故 (ii) 不可能；若强行选一个 effective D 补足 +80.55，必须说明 D 来自 C9 Theta-pilot，否则是 arbitrary height。

## 8. Conclusion / next tasks

1. Height/Faltings dictionary 是 formable，但 current data 下 **Q_C≤h_C 的 naive positivity 不成立**：b=3 B=O_K deficit 93.71 natural 大于 arch max 13.16；b=273 更大；B=I 只给 conditional surplus。
2. 任何 height proof 必须增加一个 explicit positive effective cycle/line bundle/height term；当前 C9 `h_C` 没有这个项。不是 TC 的替代。
3. 下一步实际计算：识别 theta divisor/Faltings line bundle 的 extra positive degree；对 b=3/B=O_K 计算其 local Green function；若 extra term 不能从 source 得到，则 height route **impossible** from current data，应回到 TC/G0-G3。
4. 不能在 height 中任意放大 B=I、auxiliary E、arch metric 或选择 effective divisor；这会违反 no arbitrary assumptions。

## 9. Status

Stage1 natural-language/arithmetic；无 Lean/Project/kernel/comparator/独立审查；target_accepted=false；P6 open。没有把 H-F 的 (i)-(iii) 当作已证；没有 arbitrary height/effective divisor。

