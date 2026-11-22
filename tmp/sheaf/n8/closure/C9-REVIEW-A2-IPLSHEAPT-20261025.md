# C9 adversarial review：A2 ratio identity

任务：task-410（Adversarial review of A2 ratio identity）。owner：iplsheapt。日期：2026-10-25。只做 accept/reject；不重写 A2；不改 Lean/Project/目标；只写本文件。No mixed/E3。

被审对象：C9-P6-CAN-NATURAL-PROOF-20261025.md §3 Lemma A2：

```
L_H = det^{⊗M}(E_H) ⊗ det^{⊗M}(O(−))^{−1};
deg(L_H)/M = deg(det E_H) = μ_log(H(C)) = h_can;
deg(L_q) = Q_can.
```

## 0. Verdict

**A2 不能被接受为 exact proof；只能接受为一个 conditional schema。** 决定性的 reject 点：

```
(R1) E_H rank>1 只被引用，未构造；
(R2) M（positive tensor power）没有 formula/existence proof;
(R3) deg(O(−))=0 未证明，可能是隐藏 factor;
(R4) deg(det E_H)=μ_log(H) 未显示 rank/normalization，可能隐藏 1/r 或 r;
(R5) common normalization 的 rescaling invariance 不能证明绝对 equality.
```

因此 A2 的 ratio identity 不是 smooth exact identity；它依赖 A2-G1–G7（E_H/det、O(-)、M、N_v、hull approximant、vertical shift、tensor twist）。源文本只引用 Ob1-Ob3/Prop3.9，占位为 “standard normalization”，没有显示这些因子。

## 1. Step-by-step accept/reject

| step | claim | verdict | exact reason |
|---|---|---|---|
| A2-S1 | H determines arithmetic vector bundle `E_H` rank>1 over 1-column local rings. | **REJECT as proof / CONDITIONAL** | Rem3.9.5(Ob1)-(Ob2) is a reference/representation, not an explicit construction; rank and localizations are not displayed. |
| A2-S2 | `L_H=det^{⊗M}(E_H)⊗det^{⊗M}(O(−))^{−1}`. | **REJECT** | `M` is not defined; positivity/divisibility and `O(−)` inverse normalization are asserted, not proved. |
| A2-S3 | `deg(O(−))=0` (so O(-) adjustment degree zero). | **REJECT** | No source equality displayed. In a nontrivial arithmetic determinant normalization `O(−)` can carry a degree/constant; the claim that it is zero must be proved, not assumed. |
| A2-S4 | `deg(det E_H)=μ_log(H(C))`. | **REJECT** | If `μ_log` is a total log-volume and `E_H` rank r, determinant degree may include r (or the definition may divide by r); the source's Ob3-3 'arithmetic degree=log-volume' is a reference, not the displayed exact identity. Hidden rank/normalization factor unresolved. |
| A2-S5 | `deg(L_H)/M=deg(det E_H)`. | **CONDITIONAL** | Algebraically true if `deg(det^{⊗M}E)=M deg(det E)` and O(-) degree0; both antecedents are S2/S3. |
| A2-S6 | `deg(L_q)=Q_can` for q-pilot line bundle. | **ACCEPT conditional** | Rank-one q-pilot; Prop3.9/A1 normalization gives it. It still depends on A1 and the source normalization, not on this file. |
| A2-S7 | common normalization; rescaling ν'=cν scales both sides by c. | **ACCEPT only invariance** | This proves the inequality is invariant under a common rescaling; it does **not** prove the absolute equality `deg(L_H)/M=h_can` or fix c. Different normalizations of det/log-volume give different constants. |

## 2. Hidden factors / exact missing statements

### 2.1 rank factor

If `rank(E_H)=r>1`, then for the determinant line bundle

```
deg(det E_H) = rank-normalized degree? or total degree?
```

The source must specify whether `μ_log(H)` is the total arithmetic degree of `det E_H` or the slope `deg(det E_H)/r`. A2 writes `deg(det E_H)=μ_log(H)` with no r. This is a hidden factor unless Ob3-3 defines `μ_log` as total determinant degree. The current text does not display that definition.

### 2.2 O(-) adjustment

`det^{⊗M}(O(-))^{-1}` is not the trivial line bundle. A2 asserts `deg(O(-))=0` from Prop3.9(i) (which says log(O)=0). That only fixes the **structure sheaf** log-volume, not necessarily the determinant degree of `O(-)`; the inverse/twist may carry a nonzero constant/normalization. Exact degree-zero is unproved.

### 2.3 M exponent

`M` is introduced as a positive tensor power with “M sufficiently divisible” to trivialize localizations. No formula for M, no proof such M exists, and no proof that dividing by M is compatible with the source's log-volume normalization. A2 uses `/M` before establishing M≠0/positive integer and its relation to rank/weights.

### 2.4 normalization constant

A2 says both sides measured in same scale; under `ν'=cν` both sides scale by c. This is homogeneity, not equality. The absolute constant c between C9 canonical normalization and the determinant degree is exactly T_can/normalization data; A2 does not compute it. If c≠1, the ratio identity is off by c.

### 2.5 q-pilot side

`deg(L_q)=Q_can` is rank-one and plausible from A1/Prop3.9, but it is still conditional on A1's q-pilot coric normalization and on the same absolute scale. It cannot repair the h side's hidden factors.

## 3. Consequences

A2's identity is **not** a free-standing exact theorem. The correct status is:

```
A2 = conditional schema:
  assume E_H, rank r, M, O(-) degree, det/log-volume equality, common normalization;
  then the ratio identity follows by determinant algebra.
```

The exact missing equalities are A2-I1–I8 plus the rank/normalization constant c. Without them, the claimed exact chain `deg(L_H)/M=...=h_can` is not established. P6_can cannot use A2 as a proved equality.

No counterexample is constructed; this is an adversarial rejection of exactness, not a disproof of the intended source theorem. The source references Ob1-Ob9 may contain the missing details, but the current A2 text does not display them; citing them is not a proof.

## 4. Accept/reject summary

| part | status |
|---|---|
| E_H/rank construction | REJECT as proof (conditional reference) |
| det^{⊗M}/O(−) definition | REJECT (M/O(-) unresolved) |
| deg(O(−))=0 | REJECT |
| deg(det E_H)=μ_log(H) | REJECT (rank/normalization hidden) |
| deg(L_H)/M=deg(det E_H) | CONDITIONAL on S2/S3 |
| deg(L_q)=Q_can | ACCEPT conditional |
| rescaling invariance | ACCEPT only invariance, not absolute equality |
| A2 as exact ratio identity | **REJECT** |
| P6_can via A2 | NOT established |

## 5. Conclusion

A2's ratio identity is rejected as an exact proof. The algebra `deg(det^{⊗M}E)/M=deg(det E)` is fine once M and determinant degree are defined and O(-) has degree0, but the current A2 does not establish those hypotheses and hides potential rank and normalization factors. The q-pilot side is acceptable only conditionally. Therefore A2 remains a conditional schema; P6_can is not proved from it. No rewrite of A2 is performed; no mixed/E3; no Lean edits; P6 open.

