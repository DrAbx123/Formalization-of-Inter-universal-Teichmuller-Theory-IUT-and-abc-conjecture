# C9 B=I possible-image region inside the target hull

Task: task-272. Date: 2026-10-25. Author: transport.
Short theorem/proof. No arbitrary region; no Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-TAME-LOG-DOMAIN-20261025.md | 250 | 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06 |
| C9-ARCH-LOWER-S3-20261025.md | 162 | 3847F1DEE3F3F73322A2F5F74E5ECC936E3FF0113BA3319FF76EA1D20904F73F |
| C9-NEW-BI-SOURCE-20261025.md | 234 | A90CC1B516A9AFC784A20A8CE2FAFB6CF16752459D73562D36C3093B85B294B3 |
| C9-MASTER-CONTRADICTION-20261025.md | 1022 | 19C5D1C6A4D3768C1E593249DF4F93435409CABEF558341186C1FA7E0DA72A43 |

## 1. Object and verdict

For b=3, B=I, the source-generated local region is

    R_B := p^{s-r+1} J^{tensor r}                              (1.1)

on an all-bad r-tuple, as in TAME Section 6. Its normalized local volume,
after the allowed source/target transport, is

    nu_B/log p = -s+(r-1)-r/e.                                 (1.2)

For the b=3 uniform profile, the branch value used in the C9 assembly is

    h_B=(9/41) log p,   Q_p=(-3/41)log p.                     (1.3)

Question: is the actual B=I possible-image region contained in the target
holomorphic hull H_C?

Answer: CONDITIONALLY YES, BY DEFINITION OF TC-B, and UNCONDITIONALLY OPEN
because neither the actual B=I source branch nor TC-B is constructed.

The inclusion is not an independent geometric theorem: H_C is defined as the
hull of the full possible-image union. If R_B is an actual possible image and
TC-B holds, then R_B subset H_C is exactly the definition of the full-union
saturation. The real missing input is the actual B=I realization and the
target-container construction, not a new inclusion estimate.

## 2. Conditional inclusion theorem

Theorem 2.1 (semantic TC-B inclusion). Assume:

(S1) the B=I branch is realized by an actual source configuration C: the
     source-generated lattices, full Ind1 orbit, and allowed Theta/BPS-gluing
     transport produce the region R_B as one of the actual possible images;

(S2) TC-B holds: H_C is the normalized holomorphic hull of the full union of
     all actual possible images (including the B=I branch and all Ind1/Ind2
     transports);

(S3) the normalized-volume identity for the transported R_B holds, with
     local value h_B=(9/41)log p for b=3.

Then

    R_B subset H_C,                                           (2.1)
    h_C >= h_B + h_inf,                                       (2.2)
    F=Q_p-h_C <= -S3 - h_inf.                                 (2.3)

Proof. (S2) says H_C contains every actual possible image; (S1) says R_B is
one. This gives (2.1). Monotonicity of normalized volume gives (2.2).
Subtracting from Q_p=-3/41 log p and using h_B=9/41 log p gives (2.3). QED.

The proof is correct but fully conditional. It contains no new estimate of
the B=I region; it is the exact semantic content of "full possible-image
union".

## 3. Consequence for P6 under the arch lower bound

Theorem 3.1. Under S1-S3 and the archimedean lower bound

    h_inf >= -S3 = -(12/41)log 12301 = -2.7563226845...,    (3.1)

the b=3 B=I profile satisfies P6:

    F=Q_p-h_C <= -S3 - h_inf <= 0,
    h_C >= Q_p.                                                (3.2)

Proof. Combine (2.3) and (3.1). QED.

Thus the desired P6 implication is valid **if both the B=I possible-image
region and the arch lower bound are available**.

## 4. Exact obstruction

None of S1-S3 or (3.1) is in the frozen source:

1. B=I actual: the branch is controlled by
   kappa=e vp(Tr y1)-vpi(y1) (task-250): kappa<=0 gives B=O_K,
   1<=kappa<=40 gives B=I, kappa>=41 ill-posed. Actual y1/Tr(y1)/kappa are
   missing; the B=I branch is not constructed. Non-filtration alpha exist but
   do not force B=I.

2. TC-B: no actual complete C/target hull H_C, no explicit full Ind1 possible-
   image union, no BPS/Theta-gluing/target column. TC-B is a target condition,
   not a proved source statement.

3. The B=I region R_B is a conditional lattice formula. Its actual source
   realization (the gamma orbit, uniformizer, tensor transport, and
   normalization) is not constructed; assigning R_B as a subset of H_C would
   be arbitrary without (S1).

4. The arch lower bound (3.1) is not proved: task-270 shows B_I-zero/IV give
   only h_inf<=A_proc, product formula gives pointwise constraints, and no
   global unit/point/B_I containment in H_C,inf is established.

Therefore:

    R_B subset H_C is CONDITIONAL on S1-S3;
    b=3 P6 is CONDITIONAL on S1-S3 plus (3.1);
    no unconditional inclusion or P6 follows.

No concrete failure of the inclusion is known: if TC-B and B=I actual hold,
the inclusion is definitional. The obstruction is non-realization, not a
counterexample to TC-B.

## 5. Relation to the upper-bound problem

The inclusion (2.1) gives a **lower** bound h_C>=h_B+h_inf, not an upper bound.
For P6 we need F<=0, which uses this lower bound together with h_inf>=-S3.
This is the opposite direction from the b=273 counterexample, which would
need an upper bound h_C<=H_A+h_inf. No contradiction: b=3 B=I is a P6-positive
corridor if h_inf>=-S3, while b=273 needs the missing upper bound.

Thus task-272 does not repair the b=273 upper-bound obstruction; it only
isolates the b=3 P6 route under two missing inputs.

## 6. Classification

| item | status |
|---|---|
| R_B lattice formula | CONDITIONAL source formula |
| h_B=(9/41)log p for b=3 | CONDITIONAL arithmetic |
| R_B subset H_C | CONDITIONAL on S1-S3; definitional |
| h_C>=h_B+h_inf | CONDITIONAL on S1-S3 |
| h_inf>=-S3 | NOT PROVED (task-270) |
| b=3 P6 under both inputs | PROVED CONDITIONAL |
| actual B=I | NOT CONSTRUCTED |
| actual TC-B/H_C | NOT CONSTRUCTED |
| unconditional P6 | NOT PROVED |
| b=273 upper bound | STILL MISSING |

## 7. Conclusion

The B=I possible-image region is contained in the target hull exactly when
TC-B and the actual B=I source realization hold: the inclusion is the
definition of H_C as the hull of the full possible-image union, not an
independent source inequality. Under those conditions and h_inf>=-S3, b=3 B=I
satisfies P6.

But both TC-B/B=I and the arch lower bound are missing in the frozen source.
The exact obstruction is non-realization: no actual B=I source branch, no
actual H_C/TC-B, no h_inf lower bound. No arbitrary region or r_v is chosen.
The b=273 counterexample side still needs the separate missing upper bound.

target_accepted=false.
