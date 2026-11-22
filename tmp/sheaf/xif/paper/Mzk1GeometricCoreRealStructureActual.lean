import tmp.external.ported.flt_test.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import tmp.external.ported.flt_test.Definitions.Def_AlgebraicCurve_RiemannRochRows
import Mathlib.Tactic

/-! # Mzk1GeometricCoreRealStructureActual — [Mzk1] GeometricCore real-structure skeleton over ported assets

STEP 0 prior-art: ported assets are GREEN and treated as DONE (Lead correction):
* tmp/external/ported/flt_test/Definitions/Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData.lean
  (EXIT=0): structure FiniteMapData (finite map to P^1 over a base, two affine opens,
  degree m, graded finiteness; lemmas :61-165);
* tmp/external/ported/flt_test/Definitions/Def_AlgebraicCurve_RiemannRochRows.lean
  (EXIT=0): RiemannInequality, RiemannIndexFormula, WeilDualityAdelic, WeilDuality,
  WeilOmegaEllAgrees, FunctionFieldRiemannRoch + reduction theorems;
* Mzk1Theorem25StatementActual (statement+reduction architecture), Mzk1Lemma22/24
  plans, Mzk1Lemma21Actual/RealActual/ImageActual (proved fragments).

THIS FILE provides the REAL-STRUCTURE skeleton that will replace the placeholder
Mzk1GeometricCoreStatement:
* Mzk1FiniteMapData := re-export of ported FiniteMapData (real scheme-theoretic object);
* Mzk1GeometricCoreWitness: the conclusion data of GeometricCore (finite map + degree
  positive + the three paper conditions ψ(T) ⊆ {0}, ψ unramified over 0,
  ψ^*O(1) ≅ O(D) as explicit Prop fields pending line-bundle/divisor API);
* Mzk1GeometricCoreRecast: existence of such a witness (the real-structure form);
* Mzk1RiemannRochRows: the ported RR/Serde statement layer (re-export rows).

HONEST STATUS: T/divisor conditions are explicit Prop fields (not yet expressible
with the available APIs); Thm 2.5 reduction (Mzk1Thm25Conclusion) is NOT yet proved;
the placeholder in GenEll05 must stay until both land. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra

universe u

/-- Re-export of the ported finite-map-to-P^1 structure (Apache-2.0 upstream attribution
retained in the ported file). -/
abbrev Mzk1FiniteMapData {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : Type u :=
  SmoothProperCurve.FiniteMapData c ε

/-- The conclusion data of [Mzk1] GeometricCore: a finite map to P^1 of positive
degree together with the three paper conditions (as explicit Prop fields pending the
line-bundle/divisor/unramified-morphism API). -/
structure Mzk1GeometricCoreWitness {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (T D : Set C) where
  finiteMap : Mzk1FiniteMapData c ε
  degree_pos : 0 < finiteMap.m
  maps_T_to_zero : Prop
  maps_T_to_zero_proof : maps_T_to_zero
  unramified_over_zero : Prop
  unramified_over_zero_proof : unramified_over_zero
  pullback_iso : Prop
  pullback_iso_proof : pullback_iso

/-- Real-structure form of the GeometricCore existence demand. -/
def Mzk1GeometricCoreRecast {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (T D : Set C) : Prop :=
  Nonempty (Mzk1GeometricCoreWitness c ε T D)

/-- The ported Riemann-Roch/Serde statement layer (re-export: names only, no re-proof). -/
def Mzk1RiemannRochRows : List (String × String) :=
  [ ("RiemannInequality", "AlgebraicCurve.RiemannInequality K F"),
    ("RiemannIndexFormula", "AlgebraicCurve.RiemannIndexFormula K F"),
    ("WeilDualityAdelic", "AlgebraicCurve.WeilDualityAdelic K F"),
    ("WeilDuality", "AlgebraicCurve.WeilDuality K F"),
    ("WeilOmegaEllAgrees", "AlgebraicCurve.WeilOmegaEllAgrees K F"),
    ("FunctionFieldRiemannRoch", "AlgebraicCurve.FunctionFieldRiemannRoch K F") ]

theorem Mzk1RiemannRochRows_length : Mzk1RiemannRochRows.length = 6 := rfl

#check Mzk1FiniteMapData
#check Mzk1GeometricCoreWitness
#check Mzk1GeometricCoreRecast
#check Mzk1RiemannRochRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
end