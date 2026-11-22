# C9 scope correction: mixed bad/good profiles are not the fixed uniform target

Correction note. Date: 2026-10-25. Owner: kummer.
No Lean/Project edits; no new arbitrary profile/data.
Only this file written. target_accepted=false; P6 open.

## 1. Correction

The mixed bad/good profile used in C9-MIXED-ARCH-INDEPENDENT-20261025.md
(task-313) — and in tasks 303/304/305/310/311 — is a **different profile**,
not a possible image of the fixed F_mod=Q uniform target.

Reason: IUT I Def3.1(e) uses a V-section V(K)->V_mod that selects **one**
place over each rational p. For F_mod=Q and one rational bad p, the selected
bad mass is

    rho in {0,1},

not a continuous rho in (0,1). C9-GLOBAL section1 explicitly forbids replacing
the unselected conjugates by a rho=1/2 (or other mixed) average. Task-307
confirms that changing rho is an E3 profile change, not a target-internal
variation.

Therefore the mixed-profile results are **PROFILE-CHANGE/CONDITIONAL ONLY**
and are NOT usable for original P6:

- no mixed-profile P6 rescue;
- no mixed-profile P6 counterexample;
- no mixed-profile SAT-U/U refutation;
- no mixed-profile claim about the original fixed uniform C.

## 2. What is corrected in task-313

C9-MIXED-ARCH-INDEPENDENT-20261025.md now carries a scope banner. Its
conditional theorems remain true **for the mixed profile as a different
profile**, but they do not apply to the fixed uniform target. In particular:

- "mixed m(rho)->0" is a finite mixed-profile statement;
- "mixed + B_I subset H_C,inf => P6" is a conditional statement for that
  different profile;
- "b=273 mixed + h_inf>=-S3 + m(rho)>=Q_p+S3 => h_C>=Q_p" is profile-change
  only and is not an original-P6 result.

The earlier task-311 file and tasks 303/304/305/310 have the same scope issue;
they are not to be cited as original-P6 evidence.

## 3. Uniform-profile-only status

The original target is the fixed F_mod=Q uniform profile with selected bad
places. For that target:

- uniform b=3/b=273 C1 is a LOWER bound h_C>=H_A/B+h_inf; hence
  F=Q_C-h_C<=D-h_inf, only an upper bound; no P6 counterexample (task-281/E48).
- The uniform-profile upper side SAT-U/S2 (H_C subset R_B+arch) is still
  missing; R_A subset R_B is proved (task-298), but target-upper saturation is
  not (task-290/302).
- Uniform kappa/B branch is source-undetermined (task-269/273/282); kappa
  decides B only, not the P6 sign.
- Uniform B=I b=3 gives F<=-S3-h_inf; h_inf>=-S3 is sufficient for P6 but not
  proved. Uniform B=OK gives no sign conclusion.
- Mixed-profile statements cannot be used to fill any of these gaps.

## 4. What would be usable for original P6

Only uniform-profile source theorems:

1. An upper bound h_C<=Q_C-epsilon (uniform profile) for a P6 counterexample;
2. A lower bound h_C>=Q_C, e.g. uniform finite lower + a proved arch lower
   bound h_inf>=D_p, or SAT-U/S2;
3. A uniform B=I/TC/arch theorem that gives h_inf>=-S3 and the finite branch;
4. An actual complete uniform C with all CFTH/TC/BPS/arch data.

No mixed-profile rho, conjugate average, or E3 profile change may be used as
a substitute.

## 5. Status

- Scope correction recorded; task-313 file marked profile-change.
- Mixed results retracted from original-P6 use, not as mathematics of the
  different mixed profile.
- Uniform P6: open; no proof, no counterexample; no arbitrary data.
- target_accepted=false.
