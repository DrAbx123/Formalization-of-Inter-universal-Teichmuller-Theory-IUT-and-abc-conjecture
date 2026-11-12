# S2532 non-monic transport ACTUAL; model/residue steps status

Date: 2026-11-03.

## ACTUAL

tmp/sheaf/xif/paper/S2532PairTransitiveActual.lean
  src 367342C8572FA910C9E3AF6B5857C43A9A136D9D2950EE01173599330BAB1D04
  EXIT=0
  olean FAA714B95ABC3094EB8DF26CA608A42F66AAC1CE1D589996997A234D582AF340, 165432 B
  axioms trio, no sorryAx.

New:
- S2532RootToRangeTransportNonmonic:
    for non-monic f with f.map F' = C c * psi5F, splitting, and root
    cycle type {12}, produces S2440TwelveCycleInputRequired,
  with no monicity hypothesis.  This removes hmonic from the transport.

## Step 1 (2^36 model relation): exact remaining goal

Goal:
  S2132Psi5Z.map (Int.castRingHom Q) = C (2^36) * S2057Psi5Q.

After rw [S1942_preΨ_five] and unfolding S2132Psi5Z and the curve
b-invariants, the goal is an explicit degree-12 polynomial identity over Q.
`ring_nf` normalizes most coeffs but leaves C(rational) factors; `norm_num`
does not close the polynomial identity.  Needed: coefficientwise ext with
degree bounds (or a dedicated rational-coefficient normalizer).  No fake.

## Step 2 (residue-degree-one p above 613)

Available: S2481HMod613_splits (S2481HZ splits completely mod 613 with
explicit roots), so 613 has a residue-degree-one prime in F'.
Construction route:
- use the root r (e.g. 35) and the linear factor X - r;
- apply NumberField.Ideal.primesOverSpanEquivMonicFactorsMod to get a prime
  p of O_F' above span{613} with monic residue factor X - r;
- read off inertiaDeg ℤ p = 1;
- choose P above p in O_{S2057FiveDivisionField} by Ideal.exists_ideal_over
  / lying-over.
Not yet implemented in Lean.

## Status

- non-monic transport: ACTUAL (step 4).
- step 1: exact polynomial-identity goal, automation blocked.
- step 2: construction route explicit, not implemented.
- no fake; no sorryAx.
