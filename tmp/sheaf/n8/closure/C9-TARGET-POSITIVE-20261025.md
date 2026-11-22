# C9 positive target saturation lower bound for P6

Task: task-271 (C9-TARGET-POSITIVE-20261025). Owner: logdescent. Date: 2026-10-25. Short theorem/proof attempt; only this file written; no Lean/Project/target/other-owner edits; no arbitrary region. P6 unproved; target_accepted=false.

Inputs: C9-P6-NOGO-20261025.md (E47 convention, b=273 no-go); C9-TC-EQUALITY-20261025.md (TC-C direction); C9-IND1-GLOBAL (TC-A..H/TC-S); C9-UNIFORM-HULL/GLOBAL-ASSEMBLY; C9-ARCH-HULL; task-245 variational note (sign correction below); task-262 E2.

Convention (E47): F(C)=Q_C-h_C; P6 is h_C>=Q_C, equivalently F(C)<=0. Thus F>0 is a P6 counterexample. The earlier task-245 variational note used the opposite reading of F in its title; its inequalities are used here only after this sign convention is inserted. No target data are changed.

## 0. Verdict

A canonical positive target-saturation region of the required size is constructed conditionally for the b=3 B=O_K profile, using the B=I sibling local region and the archimedean bound. It is NOT constructed for b=273.

- b=3, B=O_K selected: if target saturation TC-B includes the B=I local possible-image region and h_inf>=-S3=-2.7563226845, then
      h_C >= h_B + h_inf >= Q_C,   P6 holds.
  This is a conditional rescue from C1 insufficiency, not a proof for all C.
- b=273, B=O_K or B=I: the B=I sibling region adds only
      Delta_B=(420/41)log12301=96.471293959...
  and the IV arch container adds at most A_proc=13.164393687..., total known extra 109.635687646...,
  while the smallest required extra is D_273-A_proc=8918.010184916...; gap 8808.374497...
  No canonical target-saturation region of the required volume is constructed; the exact obstruction is the missing source theorem producing such a region (or an upper bound excluding it).

The full Ind1/full-possible-image target hull is a lower-bound object only (TC-B saturation direction); it gives no upper bound on finite possible-image volume. Therefore one cannot prove impossibility of an unknown larger target region from TC-B; one can only show that the known canonical regions are far too small and that no source construction supplies the gap.

## 1. Required positive saturation bound

Let R_sel be the selected source subfamily whose hull gives C1:

    h_C >= H_sel + h_inf,   H_sel := sum_bad alpha_p H_p^Sp log p.       (1.1)

P6 requires h_C>=Q_C. The extra volume needed beyond the C1 selected region is

    R_req := Q_C - (H_sel + h_inf) = D_C - h_inf,
    D_C := Q_C - H_sel.                                                  (1.2)

A positive target-saturation theorem must exhibit a canonical region R in H_C outside the selected subfamily with

    nu(R) >= R_req.                                                       (1.3)

No arbitrary region is allowed: R must come from the full target possible-image family (Ind1/Ind2/Ind3, BPS/Theta/gluing), with a canonical volume computation.

## 2. Canonical regions available from the target saturation

The only constructed canonical extra regions are:

(A) The B=I sibling local region. The selected B=O_K local hull has
    H_A=-411/41 log p for b=3 and H_A=-39156/41 log p for b=273; the B=I local hull has
    H_B=9/41 log p (b=3), H_B=-38736/41 log p (b=273). The difference is independent of b:

      Delta_B := H_B-H_A = (420/41)log p = 96.47129395914365... .       (2.1)

    If the full target possible-image family contains both B branches, then H_C contains the B=I local hull plus the arch component, giving the lower bound h_C>=H_B+h_inf.

(B) The IV arch container. h_inf<=A_proc=11.5log pi=13.164393687268... . This is only an upper bound on h_inf, not an extra volume of a new region. When comparing to R_req it can be used at best as A_proc in a worst-case estimate; it does not by itself add a second arch region.

(C) Full Ind1/factor-permutation saturation. TC-B says H_C is the hull of the full possible-image family, but no source theorem computes the volume of the complement beyond the selected subfamily. The symplectic-selected H_p^Sp is already in C1; any additional factor-permutation volume is not quantified. No canonical region of this type is available as a number.

Thus, for a constructive theorem, only (A) is a quantified extra region. The arch bound (B) is a cap, not a region; (C) is unspecified.

## 3. b=3 B=O_K: conditional rescue

E47 data:
    Q_p=(-3/41)log p;  H_A=(-411/41)log p;  H_B=(9/41)log p;
    D_3=Q_p-H_A=(408/41)log p=93.7149712746...;
    Delta_B=(420/41)log p=96.4712939591...;
    S_3=(12/41)log p=2.7563226845... .                                  (3.1)

The B=I sibling region exceeds the required deficit:
    Delta_B-D_3 = (420-408)/41 log p = S_3 = 2.7563226845... > 0.        (3.2)

Theorem 3.1 (conditional positive saturation, b=3).
Assume:
(S1) the target hull H_C contains the B=I local possible-image region (TC-B saturation includes both B branches), with volume H_B+h_inf;
(S2) h_inf>=-S_3=-2.7563226845... .
Then
    h_C >= H_B+h_inf >= Q_p,   i.e. F<=0, P6 holds for this C.           (3.3)

Proof. From (S1) and (S2),
h_C >= H_B+h_inf >= H_B-S_3 = (9/41)logp-(12/41)logp = (-3/41)logp=Q_p.
QED.

Notes:
- The theorem is conditional: B=I realization is unproved (task-147/149/165/184), and target saturation including the B=I region is an extra TC-B property, not a theorem for every C.
- If h_inf<-S_3, the B=I region alone does not rescue b=3; one would need an additional region of volume at least -S_3-h_inf. No such canonical region is constructed.
- If the selected C is already B=I, P6 condition is the same h_inf>=-S_3; the B=O_K selected case is the C1 insufficiency case where the sibling B=I region is needed.

This is the only known canonical positive saturation bound that can rescue b=3. It is conditional on B=I and arch data; it is not a P6 proof.

## 4. b=273: exact obstruction to the positive saturation bound

E47 data:
    Q_p=(-273/41)log p;  H_A=(-39156/41)log p;  H_B=(-38736/41)log p;
    D_273=Q_p-H_A=(38883/41)log p=8931.1745786032...;
    Delta_B=(420/41)log p=96.4712939591...;
    A_proc=13.1643936872... .                                          (4.1)

Even including the B=I sibling region and the maximal arch value, the largest known lower bound from canonical saturation is
    H_B+h_inf <= H_B+A_proc
      = (-38736/41)log p+13.1643936872... .
Its difference from Q_p is
    H_B+A_proc-Q_p
      = (38463/41)log p+A_proc
      = -8834.7032846441...+13.1643936872...
      = -8821.538890956... <0.                                         (4.2)
So the B=I+arch canonical regions still fall short of P6 by 8821.54.

Equivalently, the smallest required extra volume (at h_inf=A_proc) is
    R_req,min = D_273-A_proc = 8918.010184916...,
while the largest known canonical extra (B=I plus arch cap) is
    Delta_B+A_proc = 109.635687646...,
leaving gap
    8918.010184916...-109.635687646... = 8808.374497... >0.             (4.3)

Obstruction theorem 4.1 (conditional/exact).
Under the currently constructed target-saturation regions (selected source subfamily, B=I sibling, IV arch cap), there is no canonical region R with nu(R)>=R_req for b=273. The gap is at least 8808.37 natural units. Therefore the positive target-saturation method cannot prove P6 for b=273 from these constructions.

This is not a proof that no unknown target possible image of sufficient volume exists. TC-B defines H_C as the hull of the full possible-image family; an unknown possible-image family could in principle contain a larger region, but no source theorem constructs it or bounds its volume. The exact obstruction is the absence of such a construction (and of an upper bound on the complement). An arbitrary enlargement of H_C would violate TC-B/source constraints and is not allowed.

## 5. Why full Ind1/gluing does not immediately give the region

TC-B says the full possible-image family is larger than the selected source subfamily, but it does not give a volume for the complement. The full Ind1 group is a procession automorphism group, not a finite label translation; its orbit of a region may be larger, but:
- the orbit's normalized volume depends on the target-container normalization and on the same finite q/BPS data;
- no source theorem computes the orbit hull volume beyond H_p^Sp;
- IV caps only the archimedean direction; it does not produce a finite region of volume ~8800.

The B=I sibling is the only quantified next region, and its increment Delta_B=96.47 is b-independent: it cannot scale with b=273. The arch cap is at most13.16. Hence the known target saturation cannot bridge the 8800 gap. A new theorem would have to construct a finite target possible-image region with normalized volume at least 8808 (for b=273), not merely use TC-B formally.

For b=3, the B=I sibling increment 96.47 just exceeds D_3=93.71, so the same mechanism conditionally works if the arch sign condition h_inf>=-S_3 holds. This is the sharp positive-saturation rescue and its exact boundary.

## 6. Proved / conditional / obstruction

Proved (conditional on E47 data and TC-B semantics):
- C1 h_C>=H_sel+h_inf.
- B=I sibling increment Delta_B=420/41 logp=96.4713, b-independent.
- b=3 conditional rescue: if B=I target region and h_inf>=-S_3=-2.7563, then h_C>=Q_p; P6 holds.
- b=273: B=I+arch max still short by 8821.5389; gap to required min extra 8808.3745.

Conditional:
- B=I is an actual target possible image / target saturation includes both B branches (TC-B extra).
- Actual h_inf satisfies the b=3 sign condition h_inf>=-S_3; no source lower bound on h_inf is established.
- Full Ind1 extra region of larger volume (not constructed).
- Complete C/CFTH/TC/arch (E2) for any profile.

Missing/obstruction:
- Canonical target region with volume >=8808 for b=273 beyond selected source subfamily;
- source theorem computing full possible-image complement volume;
- upper bound on H_C finite hull excluding such region;
- actual B=I target realization and actual arch h_inf for b=3;
- complete C and target data.

## 7. Conclusion

A positive target-saturation lower bound exists conditionally for b=3: the B=I sibling region contributes Delta_B=96.47, enough to cover D_3=93.71 provided h_inf>=-2.7563. For b=273 the same region plus the maximal arch container contributes at most 109.64, while the required extra is at least 8918.01; the gap is 8808.37. Thus the known canonical target saturation cannot rescue b=273; the exact obstruction is the missing construction (or upper bound) of a finite target possible-image region with the required volume. No arbitrary region is introduced, and P6 remains open outside the stated conditional b=3 rescue.

Only C9-TARGET-POSITIVE-20261025.md written. No Lean/Project edits. target_accepted=false; P6 conditional no-go, unconditional open.
