# C9 mixed arch task correction: uniform-profile obstruction

Task: task-315 (Retasked after scope correction). Owner: volumedet.
Date: 2026-10-25. Short theorem/exact obstruction only. No arbitrary data,
no Lean/Project/target edits. Only this file written. `target_accepted=false`.

## 0. Scope correction

The requested mixed-profile arch lower bounds

    b=3:   h_inf >= -0.0678... log p
    b=273: h_inf >= -5.6759... log p

come from the mixed bad/good profile rho=1/2. That profile is a **different
profile**, not a possible image of the fixed F_mod=Q uniform target:

- IUT I Def3.1(e)'s V-section selects one place per rational p, so the
  selected bad mass at a rational p is rho in {0,1}, not a free rho in (0,1).
- C9-GLOBAL §1 explicitly forbids replacing the unselected conjugate places
  by a rho=1/2 average.
- Task-307 classifies the mixed profile as the E3 profile change.

Therefore task-303/304/305/310/311/313 mixed-profile results are
profile-change/conditional and are NOT usable for the original uniform P6.
This file retasks to the uniform profile and records the arch obstruction
there. The mixed thresholds above are withdrawn for P6 purposes; they are
not proved or used as original-target arch lower bounds.

## 1. Uniform profile arch requirements

For the uniform F_mod=Q, e=41, p=12301 profile, the finite bad-row values
are in log-p units:

| branch | H (local h/logp) | Q/logp | P6 requires h_inf/logp >= |
|---|---:|---:|---:|
| b=3 B=O_K | -411/41 | -3/41 | D_3=408/41=9.951219512... |
| b=3 B=I | 9/41 | -3/41 | -S_3=-12/41=-0.292682927... |
| b=273 B=O_K | -39156/41 | -273/41 | 38883/41=948.3658536... |
| b=273 B=I | -38736/41 | -273/41 | 38463/41=938.1219512... |

In natural units (multiply by log12301=9.4174358389):

    b=3 B=O_K:  D_3=93.7149712746;
    b=3 B=I:   -S_3=-2.7563226845;
    b=273 B=O_K: 38883/41 logp=8931.1745786;
    b=273 B=I:  38463/41 logp=8834.7032846.

Thus the uniform P6 arch lower requirements are

    h_inf >= 93.714971... (b=3 B=O_K),
    h_inf >= -2.756322... (b=3 B=I),
    h_inf >= 8931.174579... (b=273 B=O_K),
    h_inf >= 8834.703285... (b=273 B=I).                  (1.1)

The mixed thresholds -0.0678 and -5.676 are not these values and do not
apply to the uniform target.

## 2. IV container upper bound and exact obstruction

Under the binding B_I-zero normalization, the paper-level archimedean
container gives the upper bound

    h_inf <= A = 11.5 log pi = 13.164393687268102.           (2.1)

(For b=3/273 A is independent of b.) Therefore:

- b=3 B=O_K: required h_inf>=93.714971, but h_inf<=13.164394; **impossible**
  under the IV container. The b=3 B=O_K profile remains a conditional
  counterexample with F=Q-h>=D_3-A=80.550577...>0, not a P6-positive
  profile.
- b=273 B=O_K: required 8931.17 >> A; impossible under IV.
- b=273 B=I: required 8834.70 >> A; impossible under IV.
- b=3 B=I: required h_inf>=-2.756322; the IV container gives only an upper
  bound, no lower bound. So this is not proved either; it is a conditional
  arch corridor, not a theorem.

Exact obstruction theorem 2.1. No archimedean lower bound of the form
`h_inf>=-5.676` (or `-0.0678`) is available for the uniform target from the
current source. For the uniform B=O_K b=3 and b=273 rows, the lower bound
needed for P6 is *above* the IV upper bound, so P6 cannot hold in those
profiles under the IV container. For the b=3 B=I row, the needed lower bound
is below the IV upper bound, but no source lower bound is known.

Proof. Direct comparison of (1.1) with (2.1). The B=O_K rows require
93.714971>13.164394 and 8931.174579>13.164394, contradiction with the
container upper bound. The B=I b=3 row only needs -2.756322; the IV bound
is an upper bound, not a lower bound, so it does not imply it. The b=273 B=I
row needs 8834.703285>13.164394. QED.

## 3. Why no source lower bound exists

1. IV/B_I-zero gives `H_C,inf subset pi^{j+1}B_I` and `h_inf<=A`; the
   inclusion direction is upper, not lower.
2. There is no actual archimedean possible-image hull `H_C,inf` or radial
   `r_inf` in the current corpus (task-232).
3. There is no source map from a global unit/point or `B_I` into `H_C,inf`;
   `B_I subset H_C,inf` would give h_inf>=0 but is exactly the missing
   containment, not a consequence.
4. Product formula only gives pointwise bounds for points already known to
   lie in H_C,inf; no such point is constructed.
5. Theta-gluing/BPS gives packet transport/labels, not an archimedean
   point/ball containment.

Hence no lower bound `h_inf>=-2.756322` (uniform b=3 B=I), nor any mixed
threshold, is proved.

## 4. What would prove a uniform arch lower bound

A genuine source proof would need one of:

(A) `B_I subset H_C,inf` (then h_inf>=0);
(B) a global unit `u in F^times` with `u in H_C,inf` (then h_inf>=0);
(C) a global point `x in H_C,inf` with finite valuation sum
    `-sum alpha_p v_p(x)logp >=` the required threshold;
(D) a direct construction of `H_C,inf` and computation of its normalized
    volume.

For the uniform B=O_K rows (A)-(D) would need to exceed `A`, which is
impossible under the IV container (h_inf<=A<D). Thus those rows cannot be
rescued by any arch lower bound within the source normalization; the only
way to avoid the conditional counterexample is to fail another input
(B branch/target/TC/finite donor).

## 5. Classification

PROVED (exact arithmetic and IV bound):

- Uniform arch requirements (1.1).
- B=O_K b=3/b=273 require h_inf>D>A; impossible under IV; conditional
  counterexample remains.
- B=I b=3 requires h_inf>=-2.756322; not known; B=I not actual.
- Mixed thresholds -0.0678/-5.676 are invalid for the uniform target
  (profile change).

CONDITIONAL:

- B=O_K/B=I branch actuality; finite D values; target/TC; actual H_C,inf.

IMPOSSIBLE/WITHDRAWN:

- proving the mixed thresholds as uniform arch lower bounds;
- a uniform B=O_K arch rescue within the IV container;
- using mixed profile results for original P6.

OPEN/MISSING:

- actual H_C,inf/r_inf; B_I/global point containment; B branch/TC; original
  P6.

## 6. Conclusion

Task-315's mixed-profile arch request is withdrawn as a profile change. For
the uniform target, the required arch lower bounds are `93.714971` (b=3
B=O_K), `-2.756322` (b=3 B=I), `8931.174579` (b=273 B=O_K), and `8834.703285`
(b=273 B=I) in natural units. The B=O_K rows exceed the IV upper bound
A=13.164394 and are impossible to rescue archimedeanly; the B=I rows have no
source lower bound. No mixed P6 rescue or mixed counterexample is claimed.

## 7. Status

Correction/retask short theorem only. No arbitrary r_v or rho, no Lean/
Project edits. Only this file written. `target_accepted=false`; P6 open.
