# C9 uniform-profile good/other/Ind contributions

Task: task-317, retasked after mixed-profile scope correction.
Date: 2026-10-25. Author: transport.
Short theorem/proof; no arbitrary data; no Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Scope correction

The mixed bad/good profile (0<rho<1) is a DIFFERENT profile, not a possible
image of the fixed F_mod=Q uniform target. IUT I Def3.1(e) selects one place
per rational p; the selected bad mass is rho in {0,1}. The mixed-profile
results are marked profile-change/conditional in:

    C9-MIXED-PROFILE-SCOPE-CORRECTION-20261025.md.

This file is uniform-profile only. No mixed rho is used.

## 1. Uniform setup and C1

For a fixed complete C with the uniform all-bad profile at its selected bad
prime(s), the C1 assembly is

    h_C = sum_p alpha_p h_p + h_inf(C) + E_extra(C),          (1.1)

where the first sum is over the selected bad places and E_extra collects any
other source-derived finite/global contribution (good places, other local
types, Ind1-3, target saturation). P6 is h_C>=Q_C.

The finite b=3/b=273 values are the all-bad H_A/H_B values; Q_p is the selected
bad q value. No mixed finite value is admitted.

## 2. Good places

At a selected good finite place v (i.e. v is not in the bad set), the Gaussian
generator is the unit and the tensor hull is the reference O_E. Relative to
the normalization reference its log-volume is 0. Q_C has no good-place term.
Therefore

    E_good=0.                                                   (2.1)

This is exact for the selected good places. Good places do not lower h_C below
C1.

## 3. Other local types

A selected bad place with a different local type (wild/e>=p-1, extra bad
primes, different residue degree f) is not part of the fixed uniform profile.
Using it changes the target C/profile (E3), not the original fixed F_mod=Q
uniform target. Therefore:

- if C is the fixed uniform target, E_other=0 for admissible selected places;
- if one adds other local types, the object is a different profile and the
  original P6 statement does not apply.

This is an exact scope obstruction, not a numerical bound. No arbitrary
other-local type is chosen.

## 4. Ind1/Ind2/Ind3

Within the fixed uniform profile, Ind1/Ind2/Ind3 are indeterminacies of the
target/source construction, not new local profiles:

- Ind1 procession automorphisms/permutations preserve the selected uniform
  bad profile and selected places; they transport actual possible images to
  actual possible images.
- Ind2 Ism/order-2 preserves the integral lattice.
- Ind3 is upper semi-compatibility of the log-link; it does not change the
  selected local type/profile.

If TC-B holds, H_C is the hull of the full possible-image union. Adding an
allowed possible image to a hull can only increase its normalized volume;
therefore the Ind contributions are monotone-nonnegative relative to the hull
without them. They cannot lower h_C. If TC-B is not assumed, there is no
actual target hull H_C to which an additive negative term could be assigned.

Thus Ind1-3 do not supply a negative E_extra that could lower h_C below C1.
They also do not supply the mixed rho family, which is outside the fixed
profile.

## 5. What remains

After removing mixed profiles and good/other/Ind negative terms, uniform P6 is
controlled by C1:

    P6  <=>  sum_bad alpha_p(Q_p-h_p) <= h_inf.                (5.1)

For b=3 B=I:

    Q_p=(-3/41)log p, h_B=(9/41)log p,
    P6  <=>  -S3 <= h_inf.                                     (5.2)

For b=3 B=O_K:

    F <= D3-h_inf; signing F>0 requires the missing uniform upper bound, not
    a positive good/other term.                                (5.3)

For b=273 all-bad: both B branches give F bounds needing the missing upper
bound (task-267); good/other/Ind do not change that.

The remaining obstructions are exactly:

- actual B/I branch and H_A-full/kappa;
- actual TC-B/target H_C;
- actual archimedean h_inf lower bound (h_inf>=-S3 for b=3 B=I);
- uniform profile upper bound for b=273;
- complete C/TC.

## 6. Theorem

Theorem 6.1 (uniform C1 reduction). For the fixed uniform target:

(a) good selected places contribute E_good=0;
(b) other local types contribute E_other=0 if admissible; otherwise they are
    a profile change outside the original target;
(c) Ind1/Ind2/Ind3 are monotone hull operations, not additive negative terms;
(d) consequently no good/other/Ind contribution lowers h_C below the C1
    value sum_bad alpha_p h_p+h_inf.

Proof. (a) is the reference unit region. (b) is IUT I Def3.1(e) and the fixed
profile. (c) follows from hull monotonicity under allowed possible-image
additions; without TC-B the target hull is not defined. (d) combines (a)-(c).
QED.

This theorem is a reduction, not a P6 proof: the C1 value itself can be below
Q_C, and h_inf is uncontrolled.

## 7. Conclusion

For the uniform target, good places are exactly zero; other local types are
profile changes and do not belong to the original fixed C; Ind1-3 are
monotone hull operations, not negative additive contributions. Therefore the
mixed-profile good/other-class rescue is not available for the original P6,
and no good/other/Ind term can lower h_C below C1.

The remaining uniform P6 gaps are the actual B/I branch, TC-B/H_C, and the
archimedean lower bound h_inf>=-S3 (plus the b=273 upper bound). No arbitrary
profile, r_v or local type was chosen.

target_accepted=false.
