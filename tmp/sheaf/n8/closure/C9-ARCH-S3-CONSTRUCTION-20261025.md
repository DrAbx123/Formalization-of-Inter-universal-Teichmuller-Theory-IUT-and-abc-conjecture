# C9 arch S3 construction：h_inf ≥ −S3 via explicit arch hull/global unit

任务：task-371（h_inf≥−S3 via explicit arch hull/global unit）。owner：iplsheapt。日期：2026-10-25。短证明/构造或 exact gap；不改 Lean/Project/目标；不引入 arbitrary r_v；只写本文件。No mixed/E3。

输入：C9-NEW-HULL-UNIT-20261025.md（task-249）；C9-ARCH-BI-POSSIBLE-20261025.md（task-363）；C9-ARCH-HULL-20261025.md；C9-ARCH-ACTUAL-RINF-20261025.md；C9-P6TRUE-RB-HULL-20261025.md；C9-B3-BI-CORRIDOR；C9-ARCH-S3-BIREGION。

## 0. Verdict

**没有从 source 构造出实际 H_C,inf，也没有构造出落入 H_C,inf 的 global unit/point；h_inf≥−S3 未证。** 可证的只是条件性 product-formula reductions：

```
(A) B_I ⊂ H_C,inf  ⇒ h_inf ≥ 0;
(B) a global unit region ⊂ H_C,inf ⇒ h_inf ≥ 0;
(C) a global point region x⊂H_C,inf with Σ α_p v_p(x)logp ≤ S3 ⇒ h_inf ≥ -S3.
```

Current source supplies none of the three inclusions/maps. Therefore the b=3 B=I P6 route via R_B⊂H_C plus h_inf≥−S3 remains conditional. Exact obstruction is non-realization: no actual H_C,inf/r_v/angular data, no B_I possible-image theorem, no global unit/point-to-hull map.

If (A)/(B)/(C) held together with actual B=I and R_B⊂H_C:

```
R_B⊂H_C ⇒ h_C≥H_B+h_inf;  H_B=9/41 logp, Q=-3/41 logp, S3=12/41 logp;
h_inf≥-S3 ⇒ h_C≥H_B-S3=Q;  b=3 P6 holds.
```

## 1. Explicit arch hull is missing

H_C,inf is the archimedean component of the target holomorphic hull. IV provides only

```
H_C,inf ⊂ π^{j+1}B_I,   logvol(B_I)=0;  h_inf ≤ A_proc=11.5logπ.
```

The actual `r_v`, angular terms, and complex uniformization of H_C,inf are not constructed. There is no source theorem identifying H_C,inf with B_I or any explicit ball/region whose log-volume can be computed. Choosing a radius/region would be an arbitrary r_v, prohibited.

## 2. Global-unit / point candidates

| candidate | global? | arch absolute values | map to H_C,inf? | product formula |
|---|---|---|---|---|
| 1∈F | yes | 1 | not supplied | would give h_inf≥0 |
| i∈F | yes | 1 | not supplied | would give h_inf≥0 |
| E[6] torsion over F | yes | 1 (roots of unity) | no source map | would give h_inf≥0 |
| qUnit | no (local q-pilot) | local | no | not applicable |
| p^{-1}/q-root | no global point | local | no | arbitrary |

For any global `x`, product formula gives

```
h_inf ≥ Σ_v|∞ α_v log|x|_v = -Σ_p α_p v_p(x)logp.
```

A global unit (`v_p(x)=0`) gives h_inf≥0; a point with finite weighted valuation sum ≤S3 gives h_inf≥−S3. But this requires the arch profile/region of x to be contained in H_C,inf. H_C,inf is an archimedean tensor packet/log-hull, not a subset of F or E_j(F); no canonical map sends 1, i, or E[6] torsion into it. Merely being global or a unit does not put a point in the hull.

The local qUnit is particularly not usable: it is a finite local q-pilot unit, not a global element; it has no arch components in F. The E[6] torsion points are global but have no source-defined arch hull image, and their finite valuations are not units. The global unit i has arch |i|=1 but no source map to H_C,inf. These are exact obstructions, not choices.

## 3. B_I as possible image

If B_I itself were an actual possible image, monotonicity would give h_inf≥0, stronger than needed. But IV only supplies the upper container H_C,inf⊂π^{j+1}B_I; B_I-zero is a normalization, not an inclusion. No source theorem says B_I is an actual possible image. The archimedean Θ-pilot definitions do not determine the actual hull or its radius.

## 4. Conditional theorem and exact gap

**Theorem 4.1 (conditional).** If either (A) B_I⊂H_C,inf, (B) a global unit region lies in H_C,inf, or (C) a global point with finite valuation sum≤S3 lies in H_C,inf, then h_inf≥−S3. Moreover, if actual B=I and R_B⊂H_C hold, then b=3 P6 follows.

Proof. (A)/(B) give h_inf≥0 by monotonicity/product formula; (C) gives h_inf≥−Σα_p v_p(x)logp≥−S3. Then h_C≥H_B+h_inf via R_B inclusion, and H_B−S3=Q. QED

**Exact obstruction:** none of A/B/C is in the frozen source. In particular:

```
(O1) actual H_C,inf / r_v / angular terms not constructed;
(O2) no theorem B_I is an actual possible image;
(O3) no global unit/point-to-H_C,inf map or arch region containment;
(O4) B=O_K/B=I/H_A-full and R_B⊂H_C remain conditional.
```

No counterexample `h_inf<−S3` is constructed either: the actual arch hull is unknown. Thus this is a gap, not a disproof.

## 5. Classification

| item | status |
|---|---|
| IV upper H_C,inf⊂π^{j+1}B_I | PROVED conditional source |
| actual H_C,inf/r_v/angular | MISSING |
| B_I actual possible image | NOT PROVED |
| global unit/point in H_C,inf | NOT PROVED |
| product formula implication (C) | PROVED conditional |
| h_inf≥−S3 | NOT PROVED |
| b=3 P6 under B=I/R_B/h_inf≥−S3 | PROVED conditional |
| actual b=3 P6 | NOT OBTAINED |
| counterexample h_inf<−S3 | NOT CONSTRUCTED |

## 6. Conclusion

No explicit arch hull or global unit/point is constructed, so h_inf≥−S3 is not proved. The only valid statements are conditional product-formula reductions: B_I inclusion or a global unit region gives h_inf≥0; a global point with finite weighted valuation sum≤S3 gives h_inf≥−S3. None has a source map into H_C,inf. B_I is only an upper-container/normalization object, not an actual possible image. Therefore b=3 B=I P6 via h_inf≥−S3 remains conditional. No arbitrary r_v, no mixed/E3, no Lean/Project edits; P6 open.

