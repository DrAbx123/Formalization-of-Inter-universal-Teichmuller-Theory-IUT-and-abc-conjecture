# C9 NPC/M3 scope correction: uniform profile only

Scope correction requested by Lead. Owner: logdescent. Date: 2026-10-25. Correction note only; no Lean/Project/target/other-owner edits; no arbitrary data. Only this file written.

## 0. Correction

The TAME §5 mixed bad/good profile is a **different profile**, not a possible image of the fixed F_mod=Q uniform target.

Reasons, exactly as in the Lead correction and task-307:
- IUT I Def3.1(e): V is a section of V(K)->V_mod; for F_mod=Q each rational p has one selected place, so the bad mass at a rational p is in {0,1}. There is no second selected conjugate place at the same p to carry a mixed rho=1/2 factor.
- C9-GLOBAL §1 explicitly forbids replacing unselected conjugate places by a new rho=1/2 average to avoid the uniform case.
- TAME §5 mixed-profile construction uses a tuple with some good factors at the same p; it is a different admissible profile/C, an E3 profile change, not an element of the fixed all-bad uniform H_C.

Therefore the mixed-profile formulas, numerical bounds, and mixed-P6/counterexample/U talks are NOT usable for the original P6 target. They are profile-change/conditional objects only.

## 1. Effect on C9-NPC-M3-20261025.md

The task-307 file already concludes that the task-299 mixed region is not a possible image of the fixed uniform C and that NPC is not disproved by it. This correction note makes the scope explicit for every mixed-profile passage:

- The mixed rho=1/2/b=273 number h_mix≈-9.2538 natural in that file is a **profile-change scenario**, not a target possible-image height and not a P6 rescue.
- The conditional statement "if the mixed region were in H_C" is withdrawn as a P6/U claim; it is only an E3 illustration.
- No mixed P6 rescue, mixed counterexample, mixed U refutation, or mixed NPC countermodel is claimed. Task-299's mixed non-generation statement is a different-profile statement, not a countermodel to NPC for the fixed F_mod=Q uniform C.
- The uniform-profile conclusion of task-307 stands: NPC/M3 is not proved for the fixed uniform target; no source-valid extra region beyond R_B+arch is constructed; U/b=273 F≥8821 remains conditional on NPC/U; P6 open.

## 2. Uniform-profile scope for continuation

From now on, for the original P6 only the uniform profile is used:
- F_mod=Q, one selected rational bad p, bad mass rho=1, all selected factors at p bad;
- no mixed rho averaging, no mixed good-factor Gaussian permutation as a target possible image, no mixed-profile P6 inequality;
- row/Theta weights, q/BPS/target column, and TC-A..H/TC-S as in the uniform C9 profile;
- TAME §6 B=O_K/B=I row classification and the B=I region of task-274 are within the uniform profile and remain applicable;
- NPC/M3, U3/U273, the h_inf split, and the b=273 conditional counterexample remain conditional as stated in tasks 293/300/307.

Mixed-profile results (tasks 303/304/305/310/311/313 and task-299 mixed passages) are excluded from the original P6 route. They may be cited only as different-profile (E3) research, never as target P6 evidence.

## 3. Status

No claim of this note changes the source target or creates new data. The correction is a scope/classification statement:
- mixed bad/good profile: DIFFERENT PROFILE, NOT TARGET POSSIBLE IMAGE;
- mixed P6/U/NPC conclusions: WITHDRAWN as P6 statements, E3 only;
- uniform NPC/M3: NOT PROVED/NOT REFUTED, exact missing target-exhaustion remains;
- U/b=273: conditional on NPC/U; no unconditional counterexample;
- P6: open.

Only C9-NPC-M3-UNIFORM-CORRECTION-20261025.md written. No Lean/Project edits; no arbitrary data. target_accepted=false.
