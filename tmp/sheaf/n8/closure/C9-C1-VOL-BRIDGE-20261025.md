# C9 C1 volume-scaling bridge：eta equality → output D0?

任务：task-444（Bridge eta equality to output D0）。owner：iplsheapt。日期：2026-10-25。Rigorous audit；不改 Lean/Project/目标；只写本文件。No mixed/E3。

输入：C9-C1-LANA-ETA-REDUCTION-20261025.md；C9-C1-DET-20261025.md（G5 相关）；C9-C1-LITERATURE；LANA report `LANA-report-retrieved-20261023.tex` §9.2；C9-C1-ADM-NOGO。

## 0. Verdict

**G5 bridge 不成立：`eta_q=eta^anab_S` 只在 pointed real lines / volume classes 层面给 equality，不产生 multiradial output set O 中的元素 D0。** 即使 equality 加上 pilot class matching，也只得到 R^ss 中的 volume class `[M]=[q-pilot]`；R^ss 是所有 adelic measurable subsets 的 volume quotient，不是 O。没有 source theorem 把 `M=1·S`（或任意 representative）识别为 O 的输出。

因此 C1（∃D0∈O, logVol(D0)=Q）不能由 eta equality 推出；exact obstruction 是 R^ss/O 的 membership 缺失，不是 volume scaling 的算术问题。

## 1. What eta equality actually states

LANA §9.2:

```
eta_q, eta^anab_S : R^val → R^ss are pointed linear isomorphisms;
R^ss = {T⊂VC(I_uv) | adelic and measurable}/~,  T~T' iff vol(T)=vol(T');
eta^anab_S target pilot = [M], M=1·S;
eta_q target pilot = [{q_vO_v}].
```

Lemma A (C1 reduction): equality of pointed linear isomorphisms on 1D lines is equivalent to equality of their values at the pilot. Thus

```
eta_q = eta^anab_S  ⇒  [M] = [{q_vO_v}] in R^ss  ⇒  vol(M)=vol({q_vO_v})=Q.
```

This is a **volume-class equality**. It does not produce an object of O; it produces a class in R^ss and (if one chooses) the representative M=1·S. The representative M is a subset of VC(I_uv), not an output of Theorem3.11.

## 2. R^ss is not O

The multiradial output set O is the set of possible output data/regions produced by the Theorem3.11 algorithm, subject to Ind1/2/3. R^ss is a quotient of **all adelic measurable subsets** of the volume container, modulo equal volume. Therefore:

```
R^ss is much larger than logVol(O);
[M]∈R^ss does not imply M∈O or ∃D0∈O with logVol(D0)=vol(M).
```

The quotient by volume loses set-theoretic information: two subsets with equal volume are identified even if neither is an output. A class equality in R^ss cannot select an output D0 unless one proves a representative of that class lies in O.

## 3. The exact bridge conditions

To pass from eta equality to C1, one needs at least:

```
(G5-a) a representative D0 of the R^ss class [M] that lies in O;
(G5-b) a proof that D0 is an actual multiradial output (not just an adelic
        measurable subset of the volume container);
(G5-c) compatibility of the volume normalization on R^ss with logVol on O;
(G5-d) invariance under Ind1/2/3, or a canonical representative after quotient;
(G5-e) the representative's volume equals Q (not merely the class equality).
```

None is in LANA 9.2 or the C9 eta-reduction file. In particular, choosing `D0=M=1·S` would be arbitrary: M is not known to be in O.

## 4. Volume-scaling attempt and why it fails

One might try to scale S by λ to arrange vol(λS)=Q. But:

```
- λS is a subset of VC(I_uv), not automatically an element of O;
- O is not stated to be closed under arbitrary real scaling;
- choosing λ=Q/vol(S) is an arbitrary region construction, not a source output;
- the eta map equality already fixes the target class up to volume; scaling does
  not create the missing output membership.
```

Hence the volume-scaling route does not prove C1; it only produces another subset/class in R^ss.

## 5. Conditional theorem (valid only with an extra membership)

**Theorem 5.1.** If eta_q=eta^anab_S and there exists D0∈O with logVol(D0)=vol(M)=Q, then C1 holds. More compactly:

```
eta equality + (M-representative D0∈O) ⇒ C1.
```

Proof: eta equality gives the target pilot volume Q; D0∈O gives logVol(D0)=Q. QED

The extra hypothesis is exactly G5-a/G5-b; it is not supplied by A1/A2/A3 or by eta equality. Without it, the bridge is invalid.

## 6. What would prove G5

One would need one of:

```
(P1) a source theorem that M=1·S is a multiradial output region for some admissible S;
(P2) a theorem that O contains a representative of every R^ss class (or at least [q-pilot]);
(P3) an explicit construction of D0 from the eta equality, compatible with O and Ind1/2/3.
```

None is in the source corpus. No explicit counterexample is constructed; the R^ss/O type distinction is the exact obstruction.

## 7. Classification

| item | status |
|---|---|
| eta equality on pointed real lines | SOURCE-CONDITIONAL / LANA 9.2 |
| eta equality ⇒ [M]=[q-pilot] in R^ss | PROVED conditional |
| eta equality ⇒ ∃D0∈O with logVol Q | **FALSE / not implied** |
| R^ss = O | FALSE (R^ss is larger volume-class quotient) |
| M=1·S ∈ O | NOT PROVED |
| volume scaling creates output D0 | FALSE/arbitrary |
| eta + D0∈O ⇒ C1 | PROVED conditional |
| G5 bridge | **REJECTED** |

## 8. Conclusion

`eta_q=eta^anab_S` is an equality of pointed linear maps / volume classes; it implies only `[M]=[q-pilot]` in R^ss and volume Q. It does not imply the existence of a multiradial output D0∈O with logVol(D0)=Q, because R^ss is a quotient of all adelic measurable subsets, not the output set O, and no representative is proved to lie in O. The volume-scaling attempt is arbitrary. The exact missing bridge is G5-a/G5-b (representative membership in O); no source supplies it. No Lean/mixed/E3; P6 open.

