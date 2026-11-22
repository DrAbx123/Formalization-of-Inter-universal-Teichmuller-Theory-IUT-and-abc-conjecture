# C9 review：Cor3.12 Section3 hull / log-volume / Ob3-3

任务：task-418（Review hull/log-volume/Ob3-3 in Cor3.12 proof）。owner：iplsheapt。日期：2026-10-25。只做 accept/reject，不重写；不改 Lean/Project/目标；只写本文件。No mixed/E3。

被审对象：C9-COR312-UNCONDITIONAL-NL-20261025.md §3（holomorphic hull, Ob1-Ob4, det omission by Ob3-3, procession log-volume, finiteness）。

## 0. Verdict

**Section3 不能作为 unconditional/exact proof 接受；它是 source schema extraction。** 两个决定性 reject：

```
(R1) Ob3-3 的 “determinant intermediate step may be omitted” 不是已显示的 exact equality；
      rank/M/O(-)/normalization 因子未展开（同 task-410 A2 review）。
(R2) h 的 finiteness 被归约为 1,circ U_{j,vQ} 的 compactness，但 Section3 没有证明 compactness；
      这是 source-asserted input，不是 derived step。
```

其余步骤可以接受为 definitional/source-referenced conditional steps。Cor3.12 作为 source theorem 可以引用，但 Section3 的 NL proof 不是 black-box-free/unconditional derivation。

## 1. Step-by-step accept/reject

| step | claim in Section3 | verdict | exact reason |
|---|---|---|---|
| S1 | PI = union possible images; H = holomorphic hull in 1,circ U. | **ACCEPT definitional** | Consistent with Def3.8/possible-image construction; no equality claim beyond definition. |
| S2 | Remark3.9.5(i): hull is smallest subset of form `λ*O` containing the region. | **ACCEPT as source definition** | Source-level definition; caveat: non-relatively-compact regions may yield `I_Q(-)`; Section3 doesn't address this branch explicitly. |
| S3 | Ob1-Ob2: hull data represented by tensor packets of log-shells and rank>1 localizations of arithmetic vector bundles over 1-column local rings. | **CONDITIONAL / REFERENCE** | Source Ob1-Ob2 are cited, not constructed in Section3; rank/local bundle data not displayed. |
| S4 | Ob3-Ob4: determinant `det^{⊗M}` yields objects comparable to q-pilot. | **CONDITIONAL** | No explicit `E_H`, `M`, `O(-)` twist, or comparison map; source reference only. |
| S5 | Ob3-3: “for log-volume computation the determinant intermediate step may be omitted; arithmetic degree of determinant line bundle is, with suitable normalization, the log-volume of the original vector bundle.” | **REJECT as exact proof** | “with suitable normalization” is the gap. `det^{⊗M}` degree vs original bundle log-volume can differ by rank, M, O(-), and normalization constant; none displayed. |
| S6 | Procession-normalized log-volume by Prop3.9 gives `h=−|logΘ|`. | **ACCEPT conditional on Prop3.9/normalization** | Prop3.9 is source theorem; Section3 does not rederive it. If H is the source hull and normalization is packet+procession, this is a source-level identification; no factor d in canonical target. |
| S7 | xi-d: H finite after log-volume; finiteness from compactness of `1,circ U_{j,vQ}` and Prop3.9. | **REJECT as derived / ACCEPT as source-asserted only** | Compactness is not proved in Section3; Cor3.12's proof asserts compactness. Without it, `h=+∞` branch is possible and inequality may be vacuous/fail. |
| S8 | `R_{≤h}` is the set of possible output log-volumes ≤h; outputs lie in it. | **ACCEPT definitional** | Definition of set and construction of possible outputs; no numeric equality. |

## 2. Ob3-3 exactness / hidden factors

Ob3-3 is the critical weak step. Section3 states:

```
for log-volume computation the determinant intermediate step may be omitted; the arithmetic
degree of the determinant line bundle is, with suitable normalization, the log-volume of the
original arithmetic vector bundle.
```

Exact missing data:

```
(D1) E_H: rank r, localizations, determinant; not displayed.
(D2) M: positive tensor power/divisibility; no formula.
(D3) O(−) twist and inverse determinant; degree not displayed.
(D4) normalization constant c: 'suitable normalization' is unnamed.
(D5) rank factor: whether deg(det E_H) equals total log-volume μ_log(H) or r·μ_log(H)/slope; not specified.
(D6) compatibilities: tensor twist, Ind1/2/3, vertical shift; referenced Ob3-Ob4/Ob9, not proved in Section3.
```

Therefore the sentence “may be omitted” is not an exact equality as written; it is a source-computational convention whose constants/rank factors are not displayed. The Section3 log-volume identification `h=μ_log(H)` inherits this gap.

## 3. Finiteness / compactness

Section3 asserts:

```
H is finite after the log-volume computation; finiteness follows from compactness of
1,circ U_{j,vQ} and Proposition3.9; standard compactness input.
```

Problems:

1. Compactness of `1,circ U_{j,vQ}` is **asserted**, not proved/derived in Section3. IUT III Cor3.12 proof indeed uses compactness, but Section3's NL proof gives no argument.
2. If the hull is not relatively compact, Remark3.9.5 allows the whole `I_Q`, giving `+∞`; Cor3.12's statement excludes/controls this by compactness. Without proof, the finiteness claim is conditional.
3. The “finite after log-volume computation” wording does not prove `h∈R`; it assumes the compactness input.

Thus S7 is not an unconditional derivation. It can be accepted only as a citation to the source compactness statement.

## 4. Source support

Section3 cites:

```
- Remark3.9.5(i) for hull as λ*O;
- Ob1-Ob4 for vector bundles/determinant;
- Ob3-3 for degree/log-volume;
- Prop3.9 for procession-normalized log-volume;
- xi-d and compactness for finiteness.
```

These are source references, not displayed proofs. The text does not display E_H, M, O(-), normalization c, rank factor, tensor-twist compatibility, or compactness proof. Hence Section3 is **source-schema valid but not smooth exact**.

## 5. Cor3.12 unconditional claim

The source Cor3.12 can be accepted as an IUT III theorem (paper-level). But the reviewed Section3 does not establish it black-box-free: its critical determinant omission (R1) and finiteness (R2) are source-asserted. Therefore:

```
- Cor3.12 as source theorem: ACCEPT (paper citation).
- Section3 as unconditional NL proof: REJECT exactness; ACCEPT conditional schema.
- P6_can via this section: NOT established without Ob3-3 details and compactness proof.
```

## 6. Classification

| item | status |
|---|---|
| H definition / possible images | ACCEPT definitional |
| hull = λO | ACCEPT source definition (caveat IQ(-)) |
| Ob1-Ob2 bundle localizations | CONDITIONAL/reference |
| Ob3-Ob4 determinant comparison | CONDITIONAL |
| Ob3-3 det omission/degree=log-volume | **REJECT exact** |
| procession log-volume via Prop3.9 | ACCEPT conditional |
| finiteness via compactness | REJECT derived / source-asserted |
| R_{≤h} definition | ACCEPT definitional |
| Cor3.12 source theorem | ACCEPT paper-level |
| Section3 unconditional proof | **REJECT** |
| P6_can proved by Section3 | NO |

## 7. Conclusion

Section3's hull/log-volume skeleton is source-consistent, but its two critical steps are not exact: Ob3-3's determinant omission hides rank/M/O(-)/normalization factors, and finiteness is asserted from an unproved compactness input. The Section3 NL proof is therefore a conditional source schema, not an unconditional derivation. Accept the source theorem citation; reject the unconditional proof claim. No black box beyond source references; no mixed/E3; no Lean/Project edits; P6 open.

