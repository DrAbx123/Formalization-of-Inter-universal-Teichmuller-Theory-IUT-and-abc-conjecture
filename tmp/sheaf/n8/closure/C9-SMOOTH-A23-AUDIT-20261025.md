# C9 独立审计：A2/A3 是否构成 smooth exact chain

任务：task-396（Independent A2/A3 smoothness audit）。owner：iplsheapt。日期：2026-10-25。自然语言源级审计；不改 Lean/Project/目标；不引入 black-box；只写本文件。No mixed/E3。

输入：C9-P6-TRUE-NL-PROOF-20261025.md（SHA256 95731B72A1D7085C6CFC6558FA60A747C6272F6A5F5C6541AE6A42D6AFBF1281）§4 A2、§5 A3；C9-P6NORM-LEDGER-20261025.md（M1-M7/G1-G7）；IUT III Cor3.12 Step(xi-d)-(xi-f)、Remark3.9.5 Ob1-Ob9、Prop3.9、Theorem3.11(i)/Remark3.11.1(iii)。

## 0. Verdict

**A2/A3 不是 smooth exact chain。** A2 是 hull → rank>1 vector-bundle localizations → determinant tensor power → normalized log-volume 的 source-asserted comparison；A3 是 SHE 给出的 fixed q-pilot value inclusion，源文本明确保留 “perhaps only up to some sort of approximation”。两者合起来不是一组已展开的 equalities，而是至少 8 个未补的 source-asserted / approximate steps。

没有由此产生 counterexample；也没有 hidden black-box；只是 A2/A3 的 exact missing equalities/inequalities 如下。P6_norm 仍 conditional。

## 1. A2 exact chain as written

A2 的目标是证明

```
hull output → comparable quantities −|log Θ| and −|log q|;
both in R_{≤−|log Θ|}.
```

它的 proof sketch 分成四步：

```
A2(i)  hull is minimal λO region; non-relatively-compact regions → I_Q(-);
A2(ii) hull data represented by tensor packets of log-shells and rank>1 localizations
       of arithmetic vector bundles; determinant det^{⊗M}; Ob3-3 says arithmetic degree
       equals log-volume 'up to standard normalization';
A2(iii) apply procession-normalized log-volume (average over j) to hull and q-pilot;
A2(iv) 1-column log-Kummer correspondence rectifies vertical shift.
```

## 2. A3 exact chain as written

A3 的目标是

```
SHE ⇒ fixed −|log q| is one possible output log-volume:
−|log q| ∈ R_{≤−|log Θ|}.
```

它的 proof sketch：

```
A3(i)  SHE output valid relative domain and codomain arithmetic holomorphic structures;
A3(ii) permutation symmetry 0,circ U ≅ 1,circ U identifies columns up to noncanonical iso;
A3(iii) fixed q-pilot value not lost in 1-column expression;
A3(iv) inclusion is semantic, not an independent numerical computation;
       xi-f allows 'perhaps only up to some sort of approximation'.
```

## 3. Exact missing equalities/inequalities

| id | missing statement | where it would be needed | source status | provable from IUT III text? |
|---|---|---|---|---|
| S1 | `Hull(U)` exactly equals a finite `λO` region or `I_Q(-)`; +∞ branch handled. | A2(i) | Cor3.12 proof asserts compactness/finiteness; no explicit hull equality. | PARTIAL: source asserts compactness, not derived. |
| S2 | explicit determinant exponent `det^{⊗M}` with M and normalization. | A2(ii) | no display in NL; Ob3-3 referenced. | NO explicit equality in extracted text. |
| S3 | `deg(det^{⊗M}L) = M·deg(L)+O(-)` and exact equality with log-volume (constants). | A2(ii) | Ob3-3/Prop3.9 cited; source does not write constants in Cor3.12 proof. | NOT FULLY; references only. |
| S4 | exact j-normalized procession average and target normalization. | A2(iii) | Prop3.9/Rem3.1.1 cited; C6 alignment still T_norm assumption. | CONDITIONAL (T_norm). |
| S5 | 1-column log-Kummer rectification map compatible with hull/log-volume. | A2(iv) | Step(xi-d) asserts necessity; no explicit map. | NO; asserted. |
| S6 | SHE equivalence in exact sense (not merely property). | A3(i) | Rem3.11.1(iii) property; closed-loop verification not written. | NO; asserted. |
| S7 | permutation symmetry `0,circ U ≅ 1,circ U` compatibility with hull/determinant/log-volume. | A3(ii) | Theorem3.11(i) gives noncanonical iso; compatibility not separately proved. | NO; asserted. |
| S8 | exact inclusion `−|log q|∈R_{≤−|log Θ|}` without approximation. | A3(iii)-(iv) | xi-f says follows formally, with “perhaps only up to approximation” wording. | NO; approximate/semantic. |
| S9 | Ind1/Ind2/Ind3 resolution in the comparison (upper semi-compat for Ind3). | A2/A3 | Theorem3.11 definitions; no quantitative Ind3 error in III. | PARTIAL; directions asserted. |

These S1-S9 are not independent assumptions in the final intended proof, but in the NL A2/A3 file they function as **unexpanded proof obligations**. They overlap M1-M7/G1-G7 (S2/S3 ↔ M2, S6 ↔ M3, S7 ↔ M3/G2, S8 ↔ M1/G7, S5 ↔ M5, S4 ↔ M7, S1 ↔ G4/M6).

## 4. Smoothness judgement

A smooth exact chain would require each arrow to be an equality/inequality with displayed constants and no approximation. A2/A3 fail this at:

```
- determinant → log-volume: only 'up to standard normalization' (S2/S3);
- hull → compact finite region: compactness asserted (S1);
- SHE → exact output inclusion: property/semantic (S6);
- column symmetry: noncanonical iso, compatibility asserted (S7);
- final inclusion: 'perhaps only up to approximation' (S8);
- Ind3: only upper semi-compatibility, no quantitative error (S9).
```

The only arrows that are exact as stated are the definitional ones: `hull` is defined as the minimal region containing possible images; the normalized log-volume is a function of the hull; if the q-pilot value is literally in the output set, the inequality is formal. The substantive equalities (determinant/log-volume) and the exact membership are missing.

## 5. Could they be proved from IUT III text?

**Not as currently extracted.** IUT III provides the **schema** and references:

```
- Remark3.9.5 Ob1-Ob9 for hull/vector bundles/determinant/log-volume;
- Prop3.9 for procession-normalized log-volume;
- Theorem3.11(i) for permutation symmetry and Ind1/2/3;
- Step(xi-d)-(xi-f) for the determinant comparison and formal inclusion.
```

But the text does not display the determinant exponent M, the O(-) adjustment, the exact arithmetic-degree/log-volume equality, the SHE closed-loop verification, or an exact approximation-free inclusion. These remain proof obligations for a black-box-free formalization. A2/A3 are therefore **source-schema valid but not smooth exact**.

## 6. Classification

| item | status |
|---|---|
| A2 schema from Cor3.12 Step(xi-d) | SOURCE-EXTRACTED |
| A3 schema from Step(xi-e)-(xi-f) | SOURCE-EXTRACTED |
| smooth exact chain A2→A3 | **FALSE/NOT PRESENT** |
| S1-S9 equalities/inequalities | UNPROVED/ASSERTED |
| determinant/log-volume constants | MISSING |
| SHE exact equivalence | MISSING |
| approximation-free q-pilot inclusion | MISSING |
| Ind3 quantitative resolution | MISSING |
| counterexample to A2/A3 | NONE |
| black-box accepted as axiom | NONE (but source references are not expanded) |

## 7. Conclusion

A2/A3 do not form a smooth exact chain. They are a valid source-level schema but contain at least S1-S9 unexpanded equalities/inequalities: exact hull compactness, determinant exponent/normalization, arithmetic-degree/log-volume equality, procession normalization, log-Kummer rectification, SHE equivalence, permutation-symmetry compatibility, approximation-free q-pilot inclusion, and Ind3 direction. The IUT III text gives references/schema, not all expanded proofs. No counterexample or hidden black-box is introduced; P6_norm remains conditional on these obligations. No mixed/E3; no arbitrary; no Lean/Project edits; P6 open.

