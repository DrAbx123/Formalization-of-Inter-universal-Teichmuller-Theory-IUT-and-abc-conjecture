import tmp.sheaf.xif.paper.S480Example32InputActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S483Example32InputActualConstruction

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
open LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual
open Iut.SourceFinitePlaceReconstruction
open Iut.SourceModelFrobenioid

universe u
variable (K : Type u) [Field K]

/-- Universe lift on the stage divisor monoid: ULift.{u} ℕ → ULift.{u+1} ℕ. -/
noncomputable def stageDivisorULiftUp :
    StageDivisor.{u} →+ StageDivisor.{u+1} where
  toFun x := ULift.up x.down
  map_zero' := rfl
  map_add' x y := rfl

/-- The induced map on Grothendieck groups from the universe lift. -/
noncomputable def grothendieckStageULiftUp :
    Algebra.GrothendieckAddGroup (StageDivisor.{u}) →+
      Algebra.GrothendieckAddGroup (StageDivisor.{u+1}) :=
  Algebra.GrothendieckAddGroup.lift
    ((Algebra.GrothendieckAddGroup.of).comp
      (stageDivisorULiftUp))

/-- Actual divisor map: S465 lifted map followed by the universe lift. -/
noncomputable def actualDivisor
    (V : DvSmallValuationFamily (K := K))
    (X : Example32SmallBase K) :
    (example32RationalFunctionsLiftedULift (K := K)).obj X →+
      Algebra.GrothendieckAddGroup ((example32PhiIsFSM K).obj X).carrier :=
  (grothendieckStageULiftUp).comp
    (liftedDivisorMap (K := K) (L := coverField X) (V X))

theorem actualDivisor_apply
    (V : DvSmallValuationFamily (K := K))
    (X : Example32SmallBase K)
    (x : (example32RationalFunctionsLiftedULift (K := K)).obj X) :
    actualDivisor (K := K) V X x =
      grothendieckStageULiftUp
        (liftedDivisorMap (K := K) (L := coverField X) (V X) x) := by
  rfl

theorem actualDivisor_pushforward
    (V : DvSmallValuationFamily (K := K))
    (X : Example32SmallBase K) (x : ULift.{u+1} (coverField X)ˣ) :
    actualDivisor (K := K) V X (Additive.ofMul x) =
      grothendieckStageULiftUp
        (divisorMap (K := K) (L := coverField X) (V X)
          (Additive.ofMul x.down)) := by
  rw [actualDivisor_apply]
  rfl

theorem actualDivisor_naturality
    (V : DvSmallValuationFamily (K := K))
    (hV : DvSmallValuationCompatibility (K := K) V)
    (hgp : ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y)
      (z : Algebra.GrothendieckAddGroup ((example32PhiIsFSM K).obj Y).carrier),
      (example32PhiIsFSM K).gpPullback f z = z)
    {X Y : Example32SmallBase K} (f : X ⟶ Y)
    (value : (example32RationalFunctionsLiftedULift (K := K)).obj Y) :
    actualDivisor (K := K) V X
        ((example32RationalFunctionsLiftedULift (K := K)).pullback f value) =
      (example32PhiIsFSM K).gpPullback f
        (actualDivisor (K := K) V Y value) := by
  obtain ⟨u, hu⟩ : ∃ u, value = Additive.ofMul u := ⟨value.toMul, rfl⟩
  subst value
  change actualDivisor (K := K) V X (Additive.ofMul ((uliftUnitMap f) u)) =
    (example32PhiIsFSM K).gpPullback f (actualDivisor (K := K) V Y (Additive.ofMul u))
  rw [actualDivisor_pushforward, actualDivisor_pushforward]
  have hnat := divisorMap_naturality (K := K) V hV f u.down
  rw [hgp f]
  change grothendieckStageULiftUp
      (divisorMap (K := K) (L := coverField X) (V X)
        (Additive.ofMul (unitInclusionPullback f u.down))) =
    grothendieckStageULiftUp
      (divisorMap (K := K) (L := coverField Y) (V Y)
        (Additive.ofMul u.down))
  exact congrArg (grothendieckStageULiftUp) hnat

/-- Actual input data: only the valuation family and S468 compatibility remain. -/
structure Example32InputActualData where
  valuationFamily : DvSmallValuationFamily (K := K)
  compatibility : DvSmallValuationCompatibility (K := K) valuationFamily
  gpPullback_identity :
    ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y)
      (z : Algebra.GrothendieckAddGroup ((example32PhiIsFSM K).obj Y).carrier),
      (example32PhiIsFSM K).gpPullback f z = z

noncomputable def example32InputOfActualData
    (D : Example32InputActualData K) :
    Input (example32PhiIsFSM K) where
  rationalFunctions := example32RationalFunctionsLiftedULift (K := K)
  divisor := actualDivisor (K := K) D.valuationFamily
  divisor_natural := by
    intro X Y f value
    exact actualDivisor_naturality (K := K) D.valuationFamily D.compatibility
      D.gpPullback_identity f value

end LeanFormal.IUT.XiFPaper.S483Example32InputActualConstruction

end
