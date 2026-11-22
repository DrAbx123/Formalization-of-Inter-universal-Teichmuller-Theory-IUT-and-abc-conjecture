/- 
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2580P12CertificateActual
import tmp.sheaf.xif.paper.S2582P12ClosedActual
import tmp.sheaf.xif.paper.S2531Mod1249FactorActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual

/-!
# S2668: the mod-1249 root and factor-degree certificate for the S2579 task

This file supplies the two concrete arithmetic inputs needed to run the
Kummer--Dedekind argument of S2579 at the prime 1249 instead of 613:

* the explicit polynomial `S2579P12` has a root in `ZMod 1249`
  (`S2668P12Root_isRoot`, with `S2668P12Root = 45`);
* consequently the minimal polynomial of `S2579Theta`, reduced modulo 1249,
  has a root (`S2668MinpolyModRoot`);
* the reduction of `S2132Psi5Z` modulo 1249 has factor degrees `{2, 10}`
  (`S2668FactorDegrees`).

## The root modulo 1249

An external computation (and a full scan of `ZMod 1249`) shows that
`S2579P12` has exactly the twelve roots

  45, 48, 124, 127, 143, 222, 1027, 1106, 1122, 1125, 1201, 1204.

Only `45` is formalised below; the proof is a kernel-checked `decide` after
unfolding the explicit polynomial, so no `native_decide` or compiler trust is
involved.

## The minimal polynomial modulo 1249

`S2579Kummer613Actual.S2579minpolyMod` is hard-wired to `ZMod 613`.
We therefore introduce its literal mod-1249 analogue `S2668MinpolyMod`.

Unlike the mod-613 situation, `S2580_minpoly_dvd` alone is *not* enough to
transport a root of `S2579P12` to a root of the minimal polynomial: if
`minpoly Z S2579Theta` divides `S2579P12` and `S2579P12(r) = 0`, the
other factor could vanish at `r` as well.  What is needed is the equality
`minpoly Z S2579Theta = S2579P12`, which is exactly the (already proved,
olean-backed) theorem `S2582_P12Certificate` of
`S2582P12ClosedActual`.  We use that certificate in
`S2668MinpolyModRoot`.

## Factor degrees

`S2668FactorDegrees` extracts the actual two-factor certificate
`S2531Mod1249FactorDegrees_actual` (an irreducible quadratic times an
irreducible degree-ten factor) and converts it into
`factorDegrees = {2, 10}` via `normalizedFactors`.  The `change` step is
needed because `factorDegrees` is defined under its own local
`Classical.decEq`; re-elaborating the goal in a context with the same
`DecidableEq` instance (as in S2492) keeps the `normalizedFactors` arguments
syntactically aligned.

No `sorry`, `axiom`, `True`/`PUnit` gate or `native_decide` is used.  The
axiom footprints are printed at the end.
-/

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2668Mod1249RootCertificateActual

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2579Kummer613Actual
open LeanFormal.IUT.XiFPaper.S2582P12ClosedActual
open LeanFormal.IUT.XiFPaper.S2531Mod1249FactorActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

/-! ## 1. An explicit root of `S2579P12` modulo 1249 -/

/-- The chosen root modulo 1249 of the degree-twelve polynomial `S2579P12`.
The complete root set is
`{45, 48, 124, 127, 143, 222, 1027, 1106, 1122, 1125, 1201, 1204}`. -/
def S2668P12Root : ZMod 1249 := 45

/-- `45` is a root of the reduction of `S2579P12` modulo 1249. -/
theorem S2668P12Root_isRoot :
    (S2579P12.map (Int.castRingHom (ZMod 1249))).IsRoot S2668P12Root := by
  unfold S2668P12Root
  simp only [S2579P12, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.IsRoot, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  decide

/-! ## 2. The minimal polynomial of `S2579Theta` modulo 1249 -/

/-- The mod-1249 analogue of `S2579Kummer613Actual.S2579minpolyMod`, which is
hard-wired to `ZMod 613`. -/
abbrev S2668MinpolyMod (θ : RingOfIntegers S1720Field) : (ZMod 1249)[X] :=
  (minpoly ℤ θ).map (Int.castRingHom (ZMod 1249))

/-- The minimal polynomial of `S2579Theta` reduces modulo 1249 to
`S2579P12`, by the P12 certificate `S2582_P12Certificate`. -/
theorem S2668MinpolyMod_eq :
    S2668MinpolyMod S2579Theta =
      S2579P12.map (Int.castRingHom (ZMod 1249)) := by
  unfold S2668MinpolyMod
  rw [S2582_P12Certificate]

/-- The reduction of the minimal polynomial of `S2579Theta` modulo 1249 has
the root `45`. -/
theorem S2668MinpolyModRoot :
    ∃ r : ZMod 1249, ((minpoly ℤ S2579Theta).map
      (Int.castRingHom (ZMod 1249))).IsRoot r := by
  refine ⟨S2668P12Root, ?_⟩
  rw [S2582_P12Certificate]
  exact S2668P12Root_isRoot

/-! ## 3. Factor degrees of `S2132Psi5Z` modulo 1249 -/

/-- The reduction of `S2132Psi5Z` modulo 1249 has factor degrees `{2, 10}`. -/
theorem S2668FactorDegrees :
    factorDegrees (S2132Psi5Z.map (Int.castRingHom (ZMod 1249))) =
      ({2, 10} : Multiset Nat) := by
  obtain ⟨g2, g10, h2irr, h10irr, h2deg, h10deg, hprod⟩ :=
    S2531Mod1249FactorDegrees_actual
  classical
  letI : DecidableEq (ZMod 1249) := Classical.decEq _
  rw [← hprod]
  unfold factorDegrees
  change (UniqueFactorizationMonoid.normalizedFactors
      (g2 * g10)).map Polynomial.natDegree = ({2, 10} : Multiset Nat)
  rw [UniqueFactorizationMonoid.normalizedFactors_mul h2irr.ne_zero h10irr.ne_zero]
  have h2norm : UniqueFactorizationMonoid.normalizedFactors g2 =
      ({normalize g2} : Multiset (ZMod 1249)[X]) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible h2irr]
  have h10norm : UniqueFactorizationMonoid.normalizedFactors g10 =
      ({normalize g10} : Multiset (ZMod 1249)[X]) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible h10irr]
  rw [h2norm, h10norm]
  simp only [Multiset.map_add, Multiset.map_singleton]
  have hdeg2 : (normalize g2).natDegree = 2 := by
    rw [normalize_apply, Polynomial.coe_normUnit,
      Polynomial.natDegree_mul_C (Units.ne_zero (normUnit g2.leadingCoeff))]
    exact h2deg
  have hdeg10 : (normalize g10).natDegree = 10 := by
    rw [normalize_apply, Polynomial.coe_normUnit,
      Polynomial.natDegree_mul_C (Units.ne_zero (normUnit g10.leadingCoeff))]
    exact h10deg
  rw [hdeg2, hdeg10]
  decide

/-! ## 4. Axiom footprint -/

#print axioms S2668P12Root_isRoot
#print axioms S2668MinpolyMod_eq
#print axioms S2668MinpolyModRoot
#print axioms S2668FactorDegrees

end LeanFormal.IUT.XiFPaper.S2668Mod1249RootCertificateActual

end
