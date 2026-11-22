# C9 mixed-profile scope correction

Date: 2026-10-25. Author: transport.
Correction note required by the lead scope correction. No Lean/Project edits.
target_accepted=false.

## 0. Correction

The TAME Section 5 mixed bad/good profile (0<rho<1) is a DIFFERENT profile.
It is NOT a possible image of the fixed F_mod=Q uniform target.

Reason: IUT I Def3.1(e) V-section selects one place per rational prime p. For a
fixed rational p, the selected local profile is either bad or good:
rho in {0,1}. C9-GLOBAL Section 1 explicitly forbids replacing unselected
conjugate places by a rho=1/2 average or by any mixed mass.

Therefore the mixed-profile results in:

- C9-MIXED-UPPER-20261025.md (task-305);
- C9-MIXED-ARCH-BI-20261025.md (task-311);
- C9-MIXED-VOLUME-EXACT-20261025.md;
- any task-303/304/305/310/311/313 mixed construction,

are PROFILE-CHANGE/CONDITIONAL results. They are not usable for the original
uniform P6 target.

In particular:

- no mixed-profile P6 rescue is claimed for the original target;
- no mixed-profile counterexample is claimed for the original target;
- no mixed-U refutation of the uniform saturation bound is claimed;
- the mixed extra volume (38736/41 etc.) does not apply to the fixed uniform
  all-bad profile.

## 1. What remains valid for the uniform target

For a fixed uniform all-bad profile rho=1:

- TAME S6 L_A/L_B row classification for the selected bad prime(s);
- b=3/b=273 all-bad finite values;
- arch B_I-zero bound A_proc;
- the B=I inclusion conditional h_C>=h_B+h_inf (if B=I/TC-B actual);
- the h_inf>=-S3 conditional P6 route for b=3 B=I;
- the uniform-profile upper-bound obstruction (task-267).

Mixed-profile statements must be relabeled as E3/profile-change model results.

## 2. Downstream rule

Do not use mixed-profile regions as:

- possible images of the original fixed C;
- a P6 rescue or counterexample;
- a refutation of uniform saturation U;
- a bound on the uniform target hull.

They may be used only as explicit profile-change/conditional models, with the
profile change stated.

target_accepted=false.
