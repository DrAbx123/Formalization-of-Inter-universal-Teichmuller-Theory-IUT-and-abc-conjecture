# C9 new program: variational/counterexample functional F(C)=Q_C-h_C

Task: task-245 (C9-NEW-VARIATIONAL-COUNTEREXAMPLE-20261025). Owner: logdescent. Date: 2026-10-25. Creative new-math program; natural-language construction/hypothesis/theorem attempt; only this file written; no Lean/Project/target/other-owner edits; no arbitrary assumptions. P6 unproved; target_accepted=false.

Inputs: C9-GLOBAL-ASSEMBLY (corrected), C9-UNIFORM-HULL, C9-AGGREGATE-BI, C9-ARCH-SHELL-ATTACK, C9-ARCH-NORMALIZATION-CORRECTION, C9-ARCH-ACTUAL-RINF, C9-MODP-BRANCH/AUDIT (B branch conditional), C9-IND1-GLOBAL (full Ind1/TC).

## 0. Verdict

The variational program is well-posed only on a restricted conditional profile, because no actual complete C is constructed. On that profile:

1. In the B=O_K uniform b=3 profile, F(C)=Q_C-h_C is strictly positive: with B_I-zero normalization and the IV container upper bound h_inf<=A_arc=13.1644, one gets F>=D_3-A_arc=80.5506>0. This is a conditional positivity theorem.
2. In the B=I uniform b=3 profile, F(C)= -S_3 - h_inf(C), where S_3=(12/41)log12301=2.7563226845. Therefore F(C)<0 iff h_inf(C)>-S_3=-2.7563226845. The IV container gives only an upper bound h_inf<=A_arc, so it does not exclude F<0; at the container maximum F would be -15.9207.
3. The B=I branch is unproved (task-147/149/165/184: full barGamma/B branch conditional), and the actual archimedean h_inf is missing (task-232). Hence no genuine counterexample to P6 is produced. The B=I + h_inf>-S_3 configuration is an explicit conditional counterexample scenario, not an actual C.
4. The b=273 profiles are positive in both B branches under the known conditional values: B=I F= (38463/41)log12301 - h_inf ~8834.7-h_inf>0 for any h_inf<=A_arc; B=O_K even larger.
5. No compactness or stability theorem is available for the full admissible set: the moduli/field/torsion data are noncompact and discrete, F is not continuous, and no minimizer is constructed. The only unconditional-looking positivity is the conditional B=O_K profile inequality above.

The program thus suggests P6 is not refuted by current data; it isolates B=I b=3 + arch lower threshold as the unique known possible counterexample corridor. A genuine counterexample would require: (i) actual B=I realization, (ii) actual arch hull with h_inf>-S_3, (iii) all target/TC conditions. None is available.

## 1. Definition of the functional

Fix the source normalization (B_I-zero, task-171) and the target container (IV). For an admissible complete C:

    Q_C := native q-pilot global normalized log-volume,
    h_C := normalized log-volume of the holomorphic hull of the union of
           possible Theta-pilot images,
    F(C) := Q_C - h_C.                                             (1.1)

P6 asserts F(C)>=0 for every admissible C. The variational program studies inf F over admissible C, compactness of the domain, stability, and minimizers.

The functional decomposes by places:

    F(C) = sum_p alpha_p (Q_p - h_p) + sum_{v|infty} alpha_v (0 - h_v),   (1.2)

with Q only at bad finite places, weights alpha_v=d_v/[F:Q], sum alpha=1. This uses the ordinary global h_C=sum alpha h; it is not the normalized sum of local normalized volumes without weights. No U/B normalization is introduced.

## 2. Domain: no compactness, no continuity, no minimizer

The domain of admissible complete C is not compact:
- the base number field F/F_mod, the torsion fields E[6],E[41], the bad set, and the local types are discrete/unbounded data;
- the elliptic curve/field moduli and the archimedean hull vary in noncompact moduli;
- F depends on finite local q-orders and on the archimedean hull, which are not continuous functions on a compact parameter space.

Consequently there is no general existence theorem for a minimizer. A minimizer, if it exists, must be sought in a fixed finite profile with fixed F, Vbad, local types, normalization, and B branch. Even then the archimedean h_inf is only constrained by the IV upper container, so the profile domain is not compact in the negative direction.

Stability is also not available: changing C at a bad place changes the finite discrete data and Q_C; there is no proved semicontinuity of h_C under this discrete variation. The functional is a sum of local readouts, not a continuous Euler-Lagrange functional.

## 3. Reduction to the uniform profile

Restrict to the uniform profile used in the C9 computations:
- F_mod=Q, one rational bad prime p=12301, e=41, weight alpha=1;
- B=O_K or B=I conditional branch;
- b=3 or b=273;
- finite part per C9-GLOBAL;
- arch part h_inf with IV upper bound h_inf<=A_arc=11.5 log pi=13.164393687...;
- any additional good finite places have h=0 in the normalized model and do not change the comparison (they only add zero/other local data; no positive compensation is assumed).

B=O_K b=3:
    h_fin = -411/41 log p,  Q_p=-3/41 log p,
    D_3 := Q_p - h_fin = (408/41) log p = 93.7149712746...       (3.1)
    F = D_3 - h_inf >= D_3 - A_arc = 80.5505775873... > 0.        (3.2)

Thus in this profile P6 holds, conditional on the B=O_K branch, the finite deficit formula, and IV target containment. The bound is strict and has margin 80.55.

B=I b=3:
    h_fin = 9/41 log p,  Q_p=-3/41 log p,
    F = (-3/41 - 9/41) log p - h_inf
      = -S_3 - h_inf,   S_3=(12/41)log p=2.7563226845...        (3.3)
    F<0  <=>  h_inf > -S_3 = -2.7563226845...                   (3.4)

Since B_I-zero normalization gives h_inf=log(radius-like normalized readout), h_inf can be negative if the actual archimedean hull is small; there is no source lower bound h_inf>=-S_3. The IV container only gives h_inf<=A_arc. Therefore:

- if the actual B=I C has h_inf>-S_3, then F(C)<0: a genuine counterexample (under that conditional C);
- if h_inf<=-S_3, F(C)>=0: no counterexample in this corridor.
At the IV maximum h_inf=A_arc, F=-S_3-A_arc=-15.9207163718..., so the corridor is wide if B=I is actual.

B=I b=273:
    h_fin=-38736/41 log p, Q=-273/41 log p,
    F=(38463/41)log p - h_inf ~8834.7032846 - h_inf>0        (3.5)
for h_inf<=A_arc; no counterexample.
B=O_K b=273 is even more positive.

The only negative corridor in the known uniform table is therefore B=I, b=3, h_inf>-S_3. It is conditional on the unproved B=I branch.

## 4. E_j and alternative E data: why they do not produce a counterexample

E_j (task-193/198):
- actual E_j/Q with j=1/p^6, p=12301, split multiplicative I_6, q=p^6+744p^12+..., qhat order b=3;
- F=Q(i,E[6],F_sem), K=F(E[41]) source-level skeleton; C_K/C_F/V/epsilon not explicit; mod41 image exact over Q (GL2) but H over F conditional;
- B=O_K/B=I is not determined: task-165 excludes mapping-class/field sources as B=I generators; full barGamma remains unproved; task-184 classifies all B statements as conditional/invalid-as-written without H_A-full.
- arch h_inf is not determined by E_j; task-232 proves E_j complex uniformization does not give the IUT archimedean hull.

Therefore E_j gives the finite D_3/D_273 inputs but does not realize the B=I negative corridor and does not give h_inf. No genuine counterexample follows.

Alternative E (task-197/212):
- E: y^2=x^3+4x-2437249, bad at p with I_1, not I_6; v_p(q)=1; formal b=1/2, not the C9 b=3 profile;
- it has a different local type and cannot be inserted into the b=3 D_3 table; no counterexample or positivity conclusion for the C9 uniform profile follows.

The E_j/alternative E data are actual local arithmetic, but they are not a complete C; F(C) is not defined for them. Any evaluation using only D_3 and h_inf is a profile-level conditional evaluation.

## 5. Variational behavior and candidate minimizer

Within the uniform profile, F is linear in h_inf:
- B=O_K: F=D_3-h_inf, increasing as h_inf decreases; since h_inf has only upper bound A_arc, inf over the profile would be at h_inf->-infinity (F->+infinity); no interior minimizer. The maximal h_inf=A_arc gives the smallest F=80.55 (still positive).
- B=I b=3: F=-S_3-h_inf, decreasing in h_inf; h_inf->+infinity gives F->-infinity. But h_inf is bounded above by the IV container A_arc in the target, so the conditional minimum is at h_inf=A_arc: F=-15.92. If h_inf is allowed below -S_3, F becomes positive. Thus the "minimizer" is a boundary point at the container top; it is not attained by a known C.
- B=I b=273: F positive at h_inf=A_arc; h_inf would have to exceed 8834 to make F negative, impossible under IV.

The variational minimum over the full admissible set is not defined (no compactness). The profile-level candidate counterexample is the boundary configuration B=I, b=3, h_inf=A_arc; its formal F is -15.9207, but it is not a genuine C.

A formal p-variation: for B=I b=3, F(p)=-S(p)-h_inf with S(p)=(12/41)log p. For large p this is more negative even at h_inf=0; but p and the local type are fixed source data, and no admissible family of complete C with B=I is constructed. This illustrates that if B=I were realizable for large p, the functional could go negative; it does not prove a counterexample.

## 6. Stability/positivity attempts

Conditional positivity theorem (B=O_K uniform b=3):
Assume (i) the C is in the B=O_K b=3 uniform profile with the stated finite deficit D_3; (ii) its actual archimedean hull is contained in the IV container, so h_inf<=A_arc; (iii) the finite D_3 formula applies. Then F(C)>=D_3-A_arc=80.55>0.

This is the only clean positivity statement in the known profile. It is stable under small changes of h_inf (the margin is 80.55), but not under changing the B branch/b or the finite local type.

Conditional counterexample theorem (B=I b=3):
Assume (i) actual B=I; (ii) h_inf>-S_3; (iii) target/TC conditions. Then F(C)<0. This would genuinely refute P6 for that C. The assumptions are not established: B=I is unproved, h_inf is missing, and TC is unproved.

Conditional no-counterexample criterion:
For B=I b=3, if h_inf<=-S_3=-2.756, then F>=0. This is a sharp threshold; a complete C with B=I and sufficiently small archimedean hull would be positive. No source lower bound on h_inf is known.

For b=273 B=I, positivity holds for any h_inf<=A_arc (margin 8821.5); no counterexample in that row.

## 7. Proved / conditional / impossible

Proved exact/conditional:
- F decomposition and the uniform profile numbers (3.1)-(3.5).
- B=O_K b=3 positivity F>=80.55 under IV target containment.
- B=I b=3 criterion F<0 iff h_inf>-S_3; boundary value at IV max -15.92.
- B=I b=273 positivity F>0 under IV bound.
- No compactness/continuity/minimizer for the full admissible set; no actual h_inf.

Conditional:
- B=O_K/B=I branch assignments and finite D values are conditional on the corrected finite donor/TC work.
- B=I b=3 + h_inf>-S_3 is a conditional counterexample scenario; not a genuine C.
- IV target containment is required for the upper bound.

Impossible/withdrawn:
- A genuine counterexample from E_j or alternative E alone: neither is a complete C and neither realizes B=I with b=3 and an actual arch hull.
- A positivity proof for all C from the current data: the B=I corridor is not excluded.
- Using arbitrary r_v/h_inf; none is chosen. The only numerical h_inf values are the IV bound and the algebraic expression, labelled scenario.

## 8. Next executable steps

1. Determine the actual B branch for full barGamma (H_A-full; task-184/165), or prove a theorem excluding B=I.
2. Compute/construct the actual archimedean H_C,inf and h_inf for a complete C (task-232); the threshold for b=3 B=I is -2.7563.
3. If B=I is realized and h_inf>-2.7563, the variational program yields a genuine P6 counterexample; then verify TC-A..H/TC-S and target normalization.
4. If B=I is impossible or h_inf<=-2.7563, the B=I corridor closes; the B=O_K positivity theorem covers the aligned profile with margin 80.55.
5. In either case, no full P6 conclusion follows until compactness/global profile classification is done.

## 9. Conclusion

The functional F(C)=Q_C-h_C is a useful organizing object, but on current data it is defined only at profile level, not on actual complete C. The known uniform profile has a sharp conditional counterexample corridor: B=I, b=3, h_inf>-12/41 log12301=-2.7563, where F<0; at the IV container top the formal value is -15.92. The B=O_K b=3 profile is provably positive under IV target containment (F>=80.55), and b=273 is positive in both known branches. Since B=I and actual h_inf are missing, no genuine counterexample to P6 is produced; the new program's honest output is the exact criterion and the identification of B=I b=3 as the only known negative corridor.

Only C9-NEW-VARIATIONAL-COUNTEREXAMPLE-20261025.md written. Natural-language self-review done; no Lean/Project/kernel/comparator/independent review; no arbitrary assumptions. target_accepted=false; P6 open.
