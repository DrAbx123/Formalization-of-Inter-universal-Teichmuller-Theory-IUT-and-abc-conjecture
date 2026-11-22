# C9 target finite possible-image family vs Ind1 orbit of L_B

Task: task-331 (Target finite possible-image family equals Ind1 orbit of
L_B). Owner: volumedet. Date: 2026-10-25. Short theorem/counterexample only.
Uniform scope; no mixed/E3, no arbitrary data, no Lean/Project edits. Only
this file written. `target_accepted=false`.

## 0. Result

Let, for the fixed uniform b-profile,

    L_{B,j}=p^{s_j-r+1} J^{tensor r},  r=j+1,  j=1,...,20,
    R_{B,j}=Hull(L_{B,j}),  R_B=union_j T(R_{B,j}),
    H_B=(9/41)log p.                                      (0.1)

Then:

1. **Ind1 invariance of the B-row envelope:** under the constructed
   saturated row action (TAME §6), the full Ind1 orbit of L_B is contained
   in R_B (factor permutations and the B=I J-stabilization give no row
   outside L_B). This is a conditional source statement (B=I actual/transport
   + TAME row saturation), not an unconditional target theorem.
2. **Equality with the target finite possible-image family is FALSE:** the
   target family contains explicit good-finite-place possible images
   (reference O_E, normalized volume 0) which do not lie in the bad-place
   lattice family R_B. The target also contains the archimedean component,
   which is outside the finite R_B by definition.
3. The good-place counterexample has **zero normalized volume**. It disproves
   set equality but does NOT refute the volume-level NPC/U bound
   `h_C<=H_B+h_inf`. No positive-volume uniform possible image outside R_B is
   constructed; the volume NPC remains conditional on the missing global
   action factorization.
4. Therefore the implication 'equality => NPC/U => b=273 F>=8821.538' is
   conditional and not available: set equality is false, and volume
   equality/saturation is missing. No b=273 counterexample or no-go is
   claimed from this equality.

## 1. The row family and Ind1 orbit

For a fixed all-bad tuple, TAME §6 gives the saturated B=I additive lattice

    L_B=p^{s-r+1}J^{tensor r},                              (1.1)

with J=m the log lattice and r=j+1. Its hull is R_B and its normalized
finite height is

    nu(R_B,j)/log p = -s_j+j-(j+1)/41,
    H_B = (1/20) sum_j nu(R_B,j)/log p = 9/41.               (1.2)

Under the constructed row action:

- the B=I branch action preserves J and I (TAME §6/H_A-lite);
- factor permutations permute the r tensor factors of J^{tensor r};
- the prefactor p^{s-r+1} is permutation-invariant.

Hence every finite row image lies in L_B up to a factor permutation, and the
Ind1 orbit of L_B is contained in R_B after the fixed transport T:

    Ind1(L_B) subset R_B.                                   (1.3)

This is the maximal row envelope: R_A=Hull(L_A) subset R_B was proved
(TAME row inclusion), and TAME §6 excludes a third additive lattice class
for the fixed row subfamily. It does NOT classify Ind2/Ind3/BPS/Theta/global
images beyond the row action.

## 2. Equality is false: explicit good-place possible image

The target finite possible-image family contains, at a selected good finite
place v, the good Gaussian possible image:

    R_good,v=O_{E_v}  (reference integral region),            (2.1)

with normalized local volume 0 relative to the reference. This is a standard
source local profile: at a good selected place the Gaussian unit is the
profile unit and the tensor hull is the reference O_E; its normalized
contribution is zero (C9-GLOBAL/weights notes, conditional C1 local formula).

`R_good,v` is not in `R_B`: R_B is a tensor lattice at the selected bad
place p=12301, while `R_good,v` is a local region at a different finite
place. Therefore

    target finite possible-image family != Ind1 orbit of L_B.  (2.2)

Equality fails already at zero volume. Adding the archimedean component
(outside finite R_B) gives a second independent failure.

### 2.1 What this counterexample does not do

`nu(R_good,v)=0`; it does not add positive volume outside the R_B envelope
and does not refute NPC/U (`h_C<=H_B+h_inf`). It only shows that the literal
set equality in the task is false. A genuine NPC/U counterexample would need
a **positive-volume** uniform possible image outside R_B; no such image is
constructed in the uniform source scope (Ind2 Ism, Ind3 log-Kummer, BPS/Theta
and aggregate images are not explicit enough to compute an independent
positive volume).

## 3. Conditional NPC theorem if equality is replaced by volume saturation

The correct conditional statement is not set equality but:

Theorem 3.1 (row-saturation NPC, conditional). Assume:

(A1) every finite possible image has finite normalized volume in the
     R_B row envelope (no positive-volume extra row/Ind2/Ind3/BPS/Theta
     class);
(A2) the archimedean component is h_inf and all other finite contributions
     are zero or inside the envelope;
(A3) the fixed transport T and row weights preserve normalized volume.

Then `h_C<=H_B+h_inf`; for b=273,

    F=Q_C-h_C >= (38463/41)logp - A = 8821.538890956...>0,  (3.1)

while for b=3 the h_inf split remains.

However (A1)-(A3) are not the same as the false set equality and are not
proved in the source. TAME §6 saturates only the fixed all-bad row subfamily;
it gives `Ind1(L_B) subset R_B`, not `target subset R_B`. Full Ind1 is a
procession automorphism group, and Ind2/Ind3/BPS/Theta/global images are not
shown to be row transports.

## 4. Truth dichotomy

(A) **Set-level equality:** FALSE. Explicit good-place possible image
    `O_{E_v}` (volume 0) and the archimedean component are outside the
    finite R_B. Hence equality cannot be used to derive NPC/U.

(B) **Volume-level row saturation (NPC/U):** not refuted by (A); no
    positive-volume uniform possible image outside R_B is constructed. It
    remains conditional on the missing global action factorization.

(C) **Conditional NPC:** if (A1)-(A3) are supplied, b=273 gives F>=8821.538
    and b=3 gives the h_inf split. Without (A1)-(A3), no
    counterexample/no-go is obtained.

## 5. What would construct a genuine counterexample

A source-valid uniform possible image with positive normalized volume
outside R_B. Candidates and status:

- good finite places: explicit but volume0;
- archimedean component: separate and not a finite R_B row; volume h_inf,
  already part of the envelope `R_B+arch`;
- Ind1 permutations: inside R_B by (1.3);
- Ind2 Ism: no explicit positive-volume image;
- Ind3 log-Kummer: no explicit positive-volume image;
- BPS/Theta gluing: no explicit extra positive-volume image;
- other rows/local types/aggregate: not uniform fixed profile (profile
  change) or not constructed.

No such positive-volume uniform image exists in the current corpus.

## 6. Classification

PROVED/CONDITIONAL:

- L_B/R_B row formulas and H_B=9/41 logp;
- Ind1 row orbit `Ind1(L_B) subset R_B` under the saturated row action;
- explicit good-place possible image O_E outside the finite R_B, with
  normalized volume 0; hence set equality false;
- no positive-volume uniform counterexample constructed;
- conditional NPC theorem (A1)-(A3) gives b=273 F>=8821.538, not
  unconditional.

MISSING:

- global action factorization/volume saturation (A1)-(A3);
- actual target family/TC-B; actual B=I/transport; full Ind1/Ind2/Ind3/BPS/
  Theta images; actual archimedean h_inf.

IMPOSSIBLE/WITHDRAWN:

- literal equality of the target finite possible-image family with Ind1(L_B);
- deriving NPC/U from that equality;
- treating zero-volume good/arch components as a positive-volume NPC
  counterexample.

## 7. Conclusion

`Ind1(L_B) subset R_B` is the correct conditional row-envelope statement.
The target finite possible-image family is **not equal** to the Ind1 orbit of
L_B: an explicit good-place possible image O_E (volume 0) lies outside the
finite bad R_B, and the archimedean component is separate. This disproves the
literal equality but does not refute the volume-level NPC/U bound; no
positive-volume uniform possible image outside R_B is constructed. Therefore
NPC/U and b=273 F>=8821.538 remain conditional on the missing global
action factorization, not consequences of the false equality.

## 8. Status

Short theorem/counterexample only. Uniform scope, no mixed/E3, no arbitrary
data, no Lean/Project edits. Only this file written. `target_accepted=false`;
P6 open.
