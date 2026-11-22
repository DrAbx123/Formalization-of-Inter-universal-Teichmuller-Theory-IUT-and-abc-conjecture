# C9 mixed Q_full vs Q(rho): scope correction and exact uniform P6

Task: task-316. Owner: qside. Date: 2026-10-25.
Short natural-language sign/concept audit and correction; no Lean/Project edits;
only this file written.

## 0. Binding correction (read first)

The mixed bad/good profiles of TAME Section 5 are **different profiles**, not
possible images of the fixed F_mod=Q uniform target.  For F_mod=Q, IUT I
Definition 3.1(e) gives a section V -> V(F_mod): there is exactly one selected
place above each rational p, so the bad mass is in {0,1}.  C9-GLOBAL Section 1
explicitly forbids replacing unselected conjugates by an average rho=1/2 or
any other rho<1.  Task-307 confirms that inserting a mixed profile is a
profile change (E3), not a construction inside the fixed target.

Consequences:

- The target hull H_C of the fixed uniform C contains only the uniform bad
  (rho=1) possible images and its arch/good components, not TAME mixed-profile
  regions.
- Task-303's comparison of mixed H_b(rho) with the fixed target Q_full=-b/e is
  therefore **not a P6 rescue for the original target**.  Its premise "the
  mixed image lies in H_C" is false under the uniform V-section.
- Task-304's Q(rho)=-rho b/e is the native q value of a **different
  profile**, not the q-pilot Q_C of the fixed uniform C.  It is internally
  consistent for that profile but inapplicable to original P6.
- Mixed-profile results task-303/304/305/310/311/313 are marked
  profile-change/conditional and are **not usable** to claim a mixed P6
  rescue, a mixed counterexample, or a mixed U refutation.

No new attack, no arbitrary rho, no Lean.  target_accepted=false.

## 1. Which Q_C applies?

For a fixed actual C in the F_mod=Q uniform target:

    Q_C = Q_full = -(b/e) log p                                (1.1)

at the single selected bad place, where b is the q-order of the actual q-pilot
and e=41.  This Q_C is part of the source q/BPS/target data of that C; it is
not rescaled by the bad mass of an auxiliary mixed profile.

For a hypothetical E3 mixed profile with bad mass rho, one may define

    Q(rho) = -(rho b/e) log p.                                (1.2)

But Q(rho) is the native q value of **that different profile**; it is not
Q_C of the fixed uniform C.  A single C cannot simultaneously have Q_full and
Q(rho) for the same selected bad q.  Therefore:

- Q_full applies to original P6 for the uniform target;
- Q(rho) applies only to the E3 profile-consistency question;
- comparing H_b(rho) to Q_full is invalid because the mixed region is not in
  the fixed H_C;
- comparing H_b(rho) to Q(rho) is valid only for the E3 profile, not original
  P6.

The apparent task-303/task-304 inconsistency is thus a **scope/object error**,
not a normalization or sign error in the algebra:
different profiles, different Q's, and in task-303 a false hull-membership
premise.

## 2. Exact P6 for the fixed uniform target

Let C be an actual fixed uniform C with Q_C=Q_full and global normalized hull
h_C.  P6 is exactly

    P6(C)  <=>  h_C >= Q_C = -(b/e) log p.                    (2.1)

The finite B branches give:

### b=3, B=O_K

    h_fin = -(411/41) log p,  Q_p = -(3/41) log p,
    D_3 = Q_p - h_fin = (408/41) log p,
    F = D_3 - h_inf >= D_3 - A_arc = 80.5506... > 0,          (2.2)

so P6 holds conditionally under the B=O_K branch, the finite formula,
TC-B/IV container and actual arch h_inf<=A_arc.

### b=3, B=I

    h_fin = (9/41) log p,
    F = -S3 - h_inf,  S3=(12/41)log p=2.7563226845...,
    P6 <=> F>=0 <=> h_inf <= -S3.                              (2.3)

This is the exact conditional B=I threshold; h_inf is not determined by the
source (task-232/248/270/278/287).  No mixed profile changes this because the
mixed profile is not an image in the fixed H_C.

### b=273

    B=O_K finite deficit = (38883/41)log p,
    B=I finite deficit   = (38463/41)log p,
    F = D_{273} - h_inf > 0 for h_inf<=A_arc.                  (2.4)

For b=273 the conditional uniform P6 is positive under the IV container; no
mixed rescue is needed or allowed.

## 3. The mixed formulas (kept only as E3 profile information)

For the E3 mixed profile of bad mass rho,

    H_b(rho)/log p = -(1/20) sum_j rho^{j+1}(s_j+1/41),
    Q(rho)/log p = -rho b/41,
    s_j=floor(b j^2/41).

The task-304 thresholds for H_b(rho)>=Q(rho) are

    rho*_3   = 0.6627708899698342...,
    rho*_273 = 0.6298691113348261... .

These are **profile-change thresholds**, not fixed-target P6 thresholds.  In
particular they do not imply anything about H_C of the fixed F_mod=Q C, and
they do not repair or refute the exact P6 statements (2.2)-(2.4).

Task-303's comparison H_b(rho)>=Q_full has formal roots ~0.6916/0.6680, but
again it is inapplicable: the premise of membership of the mixed region in the
fixed H_C fails.  The correct conclusion is: no mixed P6 rescue, no mixed
counterexample, and no mixed target statement for original P6.

## 4. Exact obstruction / correction status

The following are withdrawn for original P6:

- task-303 "mixed profiles rescue finite positive-D obstruction" — profile
  change; H_b(rho) is not a lower bound for the fixed H_C.
- task-304 "mixed Q(rho) positive-D/no rescue" — a valid E3 profile result but
  not Q_C of the fixed uniform C.
- task-305/310/311/313 mixed-arch/U/B conclusions insofar as they use mixed
  profiles for the fixed target — profile change; not usable.
- Any comparison of mixed H_b(rho) with Q_full; any inference that a mixed
  image is in the fixed H_C; any rescaling of Q_C by rho.

Remaining exact P6 status for the fixed uniform target:

- b=3 B=O_K: conditional positivity via D_3-A_arc>0 (under the standard
  finite/IV/TC hypotheses).
- b=3 B=I: conditional on h_inf<=-S3.  The opposite corridor h_inf>-S3 would
  give F<0 but h_inf is not constructed/ bounded below; B=I branch itself
  conditional.
- b=273 B=O_K/B=I: conditional positivity for h_inf<=A_arc under the
  conditional finite rows.
- Actual complete C/BPS/Theta/TC/arch remain missing.

No arbitrary rho or mixed profile was inserted into the target.

## 5. Conclusion

The task-303 vs task-304 disagreement is resolved by scope, not algebra:
Q_full belongs to the fixed F_mod=Q uniform target; Q(rho) belongs to a
different E3 mixed profile.  The fixed target H_C does not contain E3 mixed
regions, so no mixed comparison is a P6 statement for original P6.  The exact
uniform P6 conditions are (2.1)-(2.4); the b=3 B=I threshold remains
h_inf<=-S3 for P6 and h_inf>-S3 for the conditional counterexample corridor,
with h_inf missing.  Mixed-profile documents are marked profile-change and
withdrawn from original P6.

This is the correction note required by the scope correction.  target_accepted
is false; P6 remains open/conditional.

## 6. Sources

- IUT I Definition 3.1(e) (V -> V(F_mod) section; F_mod=Q one bad place).
- C9-GLOBAL Section 1 (no averaging over unselected conjugates; uniform
  bad-profile scope).
- C9-TARGET-GENERATED-20261025.md (mixed profile is a different image class).
- C9-TAME-LOG-DOMAIN-20261025.md Section 5 (E3 mixed profile formula), Section
  7 (uniform B rows).
- C9-MIXED-PROFILE-P6-20261025.md (task-303; marked profile-change).
- C9-MIXED-VOLUME-EXACT-20261025.md (task-304; E3 profile result only).
- C9-MIXED-ARCH-BI-20261025.md / C9-MIXED-ARCH-INDEPENDENT-20261025.md
  (mixed-arch conditional, not original target).
