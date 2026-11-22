# C9 explicit B=I possible-image region R_B (b=3)

Task: task-274 (C9-BI-REGION-CONSTRUCTION-20261025). Owner: logdescent. Date: 2026-10-25. Natural-language construction/theorem attempt; only this file written; no Lean/Project/target/other-owner edits; no arbitrary region. P6 unproved; target_accepted=false.

Inputs: TAME §6 (T16b/T17b), C9-GLOBAL-ASSEMBLY (T15c, b=3 table), C9-FIXED-GLUING-SWAP (common terminal transport), C9-TC-EQUALITY/TARGET-POSITIVE, task-165/184 B-branch audit.

## 0. Verdict

An explicit **conditional** B=I region R_B for the b=3 uniform profile is constructed from the TAME B=I local lattices and the fixed-gluing row transport. It is nonempty and its local normalized height is exactly

    H_B = (9/41) log12301.                                        (0.1)

The construction is explicit in the arithmetic/lattice data and row weights. It is NOT an actual target possible-image region in the unconditioned source: the missing source object is an actual B=I generator (a real barGamma element moving the mod-p line l=O_K/J) together with its Theta-gluing transport and TC-B target saturation. Without that, R_B is a conditional branch region, not a proven subset of H_C.

No arbitrary region is introduced: every row lattice, exponent, weight, and volume is fixed by TAME (T16b/T17b) and the uniform row normalization of C9-GLOBAL.

## 1. b=3 local data

p=12301, e=41, l=41, m=(e-1)/2=20, b=3, uniform bad profile rho=1. For j=1,...,20 define

    s_j := floor(3 j^2 / 41),   t_j := 3 j^2 - 41 s_j,   1 <= t_j <= 41.   (1.1)

The B=O_K and B=I row heights from TAME (T17a/T17b) are

    nu_A,j/log p = -s_j - 1/41,
    nu_B,j/log p = -s_j + (r-1) - r/41,   r=j+1
                = -s_j + j - (j+1)/41.                               (1.2)

Exact row table:

| j | s_j | t_j | nu_A,j | nu_B,j |
|---:|---:|---:|---:|---:|
| 1 | 0 | 3 | -1/41 | 39/41 |
| 2 | 0 | 12 | -1/41 | 79/41 |
| 3 | 0 | 27 | -1/41 | 119/41 |
| 4 | 1 | 7 | -42/41 | 118/41 |
| 5 | 1 | 34 | -42/41 | 158/41 |
| 6 | 2 | 26 | -83/41 | 157/41 |
| 7 | 3 | 24 | -124/41 | 156/41 |
| 8 | 4 | 28 | -165/41 | 155/41 |
| 9 | 5 | 38 | -206/41 | 154/41 |
| 10 | 7 | 13 | -288/41 | 112/41 |
| 11 | 8 | 35 | -329/41 | 111/41 |
| 12 | 10 | 22 | -411/41 | 69/41 |
| 13 | 12 | 15 | -493/41 | 27/41 |
| 14 | 14 | 14 | -575/41 | -15/41 |
| 15 | 16 | 19 | -657/41 | -57/41 |
| 16 | 18 | 30 | -739/41 | -99/41 |
| 17 | 21 | 6 | -862/41 | -182/41 |
| 18 | 23 | 29 | -944/41 | -224/41 |
| 19 | 26 | 17 | -1067/41 | -307/41 |
| 20 | 29 | 11 | -1190/41 | -390/41 |

Checks: sum_j s_j=200; sum_j nu_A,j=-8220/41, average = -411/41; sum_j nu_B,j=180/41, average = 9/41; per-row difference nu_B,j-nu_A,j=40j/41, sum=8400/41, average=420/41. These are exact.

## 2. Explicit B=I row regions

For each row j, let r=j+1 and

    L_B,j := p^{s_j-r+1} J^{tensor r}  subset  (K_v)^{tensor r},       (2.1)

where J=m_K is the nonzero O_K-lattice (TAME J=m; the standard-lattice/orbit-generation notation is the inferred source consequence task-147). Define the row hull

    R_B,j := Hull(L_B,j)                                                (2.2)

inside the row-j tensor packet, with the standard B_I-zero normalization. Then:
- L_B,j is a full lattice: J has rank e, J^{tensor r} has rank e^r, p^{s_j-r+1} is a fractional ideal power; nonzero and free over Z_p; R_B,j is nonempty and full-dimensional.
- By TAME (T17b), normalized local height
      nu(R_B,j)/log p = -s_j + (r-1) - r/e = -s_j+j-(j+1)/41.          (2.3)
This is the explicit local B=I region for row j. It is not arbitrary: s_j,r are fixed by b=3 and the row index.

## 3. Theta-gluing and the full R_B

Let T be the common terminal packet transport of the fixed gluing (C9-FIXED-GLUING-SWAP (8)-(13)): T is a volume-preserving additive transport that sends the source row packets into the same target container, preserving row j, q/BPS labels and normalization (TC-A/TC-D/TC-E/TC-S, conditional). Define

    R_B := union_{j=1}^{m} T(R_B,j),   with the uniform row/Theta weight 1/m.  (3.1)

Because each T(R_B,j) is nonempty, R_B is nonempty. Under the C9 procession normalization (uniform rho=1; row/Theta weights 1/m; B_I-zero), the local normalized height of the row family is the weighted average

    H_B/log p = (1/m) sum_{j=1}^m [-s_j+j-(j+1)/41]
              = (1/20)(-200+210-230/41)
              = (1/20)(180/41)
              = 9/41.                                                   (3.2)

Thus R_B is an explicit nonempty possible-image row family with local height H_B=(9/41)log12301, conditional on the branch/transport. The row table and average are exact.

Relation to the B=O_K selected row family:
    nu_A,j/log p=-s_j-1/41,  average=-411/41;
    (1/m)sum_j(nu_B,j-nu_A,j)=420/41.                                  (3.3)
This is the 9/41-(-411/41)=420/41 surplus used in task-271.

## 4. What is actual and what is missing

Actual/conditional arithmetic:
- L_B,j, R_B,j and the row height (2.3) are explicit conditional source-lattice objects; the row table is exact.
- The weighted height H_B=9/41 logp follows from T17b and the uniform row normalization, given the B=I branch.
- The theta-gluing transport T is the fixed-gluing common terminal transport; its existence is the C9-FIXED-GLUING result, conditional on the corrected source gluing/TC data.
- Thus R_B is a well-defined conditional region and the height formula is proved under B=I+gluing+TC-B.

The exact missing source object:
- actual B=I realization: a real barGamma element/generator that moves the mod-p line l=O_K/J (nonzero lower first column). Task-165/184 showed that no cited source produces such a generator; H_A-full is not established, and natural alignment gives B=O_K. Without this, L_B,j is a formal TAME branch lattice, not an actual possible-image region.
- actual Theta-gluing/target saturation: TC-B must include the B=I branch in H_C; the fixed-gluing transport T must be the actual target transport (TC-A/TC-D/TC-E/TC-S).
- actual archimedean h_inf and complete C: R_B gives only the finite B=I local height; P6 rescue additionally needs the arch sign condition h_inf>=-S3=-2.7563 (task-271) and the complete C/target conditions.

No arbitrary region: the only choices are the source row index j (all rows are included with the fixed uniform weight), the B=I branch (conditional), and the fixed-gluing transport (source object). The construction does not choose an extra enlargement or a free volume.

## 5. Consequence for the b=3 target rescue

If the missing B=I source object and TC-B saturation are supplied, H_C contains R_B, so

    h_C >= H_B + h_inf = (9/41)log p + h_inf.                          (5.1)

Comparing Q_p=(-3/41)log p:

    h_C-Q_p >= (12/41)log p + h_inf = S_3 + h_inf,
    S_3=(12/41)log p=2.7563226845.                                     (5.2)

Thus P6 (h_C>=Q_p) holds iff h_inf>=-S_3=-2.7563226845. This is exactly the task-271 boundary. If h_inf<-S_3, R_B alone does not rescue b=3; a further target region of volume at least -S_3-h_inf is needed and is not constructed.

For b=273 the same B=I branch height is -38736/41 logp, and the surplus over B=O_K is still 420/41 logp=96.4713; it is far below the required 8821+ gap (task-271). R_B cannot rescue b=273.

## 6. Proved / conditional / missing

Proved (conditional on TAME B=I formulas and standard-lattice/gluing):
- Explicit row lattices L_B,j and row heights (2.3); row table exact.
- Weighted average H_B=9/41 logp; surplus over A=420/41 logp.
- Nonemptiness of R_B,j/R_B under B=I branch + transport.
- P6 condition h_inf>=-S3 for the B=O_K selected case using R_B.

Conditional:
- B=I branch is actually realized (barGamma moves l);
- Theta-gluing T and TC-B target saturation include R_B;
- complete C/TC/arch actual.

Missing/exact obstruction:
- actual B=I generator and H_A-full;
- actual Theta-gluing/target saturation inclusion;
- actual arch h_inf/TC; complete C.

## 7. Conclusion

The explicit B=I region R_B is constructed at the row-lattice level: L_B,j=p^{s_j-j}J^{tensor(j+1)} (since r−1=j), with row height -s_j+j-(j+1)/41, and the uniform row family has local height H_B=9/41 logp. This proves the arithmetic/nonemptiness part and the task-271 surplus, but only conditionally on the B=I source branch and its Theta-gluing/target saturation. The exact missing source object is the actual B=I generator/barGamma element moving l, not the region formula; no arbitrary region is introduced.

Only C9-BI-REGION-CONSTRUCTION-20261025.md written. No Lean/Project edits. target_accepted=false; P6 open/conditional.
