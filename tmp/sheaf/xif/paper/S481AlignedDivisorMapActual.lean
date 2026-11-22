import tmp.sheaf.xif.paper.S465LiftedDivisorMapActual
import tmp.sheaf.xif.paper.S480Example32InputActual
import Iut.Foundations.SourceFiniteStageModelFrobenioid
import Mathlib.CategoryTheory.Category.ULift

/-! # S481: align S465 liftedDivisorMap to universe-(u+1) Grothendieck

S465 targets `Grothendieck StageDivisor.{u}`.  S480's `DivisorialMonoidOn.{u+1}`
target is `Grothendieck StageDivisor.{u+1}`.  `StageDivisor.{u}` and
`StageDivisor.{u+1}` are both `ULift` of `ℕ`; the additive equivalence induced by
the two `stageDivisorEquivNat` maps gives the required Grothendieck map.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S481AlignedDivisorMapActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual
open LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual
open Iut.SourceFinitePlaceReconstruction
open Additive

universe u

noncomputable def stageDivisorULiftEquiv :
    StageDivisor.{u} ≃+ StageDivisor.{u+1} :=
  ((stageDivisorEquivNat : StageDivisor.{u} ≃+ ℕ).trans
    (stageDivisorEquivNat : StageDivisor.{u+1} ≃+ ℕ).symm)

noncomputable def grothendieckStageDivisorULift :
    Algebra.GrothendieckAddGroup StageDivisor.{u} →+
      Algebra.GrothendieckAddGroup StageDivisor.{u+1} :=
  Algebra.GrothendieckAddGroup.lift
    (Algebra.GrothendieckAddGroup.of.comp
      stageDivisorULiftEquiv.toAddMonoidHom)

variable {K : Type u} [Field K]

noncomputable instance coverFieldAlgebra (X : Example32SmallBase K) :
    Algebra K (coverField X) := inferInstance

variable {L : Type u} [Field L] [Algebra K L]
variable (V : DvCoverNormalizedValuationData K L)

/-- S465 divisor map aligned to the universe-(u+1) Grothendieck group. -/
noncomputable def liftedDivisorMapAligned :
    Additive (ULift.{u+1} Lˣ) →+
      Algebra.GrothendieckAddGroup StageDivisor.{u+1} :=
  grothendieckStageDivisorULift.comp (liftedDivisorMap (K := K) (L := L) V)

theorem liftedDivisorMapAligned_add (x y : Additive (ULift.{u+1} Lˣ)) :
    liftedDivisorMapAligned V (x + y) =
      liftedDivisorMapAligned V x + liftedDivisorMapAligned V y :=
  map_add _ x y

/-- Family version, conditional on an explicit valuation family. -/
noncomputable def liftedDivisorMapFamilyAligned
    (Vf : ∀ (L : DvTriangleFieldCover K) [Field L.obj.obj]
      [Algebra K L.obj.obj], DvCoverNormalizedValuationData K L.obj.obj)
    (L : DvTriangleFieldCover K) [Field L.obj.obj] [Algebra K L.obj.obj] :
    Additive (ULift.{u+1} L.obj.objˣ) →+
      Algebra.GrothendieckAddGroup StageDivisor.{u+1} :=
  liftedDivisorMapAligned (K := K) (L := L.obj.obj) (Vf L)

/-- Actual divisor field at the S480 universe: the aligned S465 map at the
cover field of X. -/
noncomputable def example32AlignedDivisor
    (Vf : LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual.DvSmallValuationFamily (K := K))
    (X : Example32SmallBase K) :
    (example32RationalFunctionsLiftedULift).obj X →+
      Algebra.GrothendieckAddGroup ((example32PhiIsFSM K).obj X).carrier := by
  exact liftedDivisorMapAligned (V := Vf X)

theorem example32AlignedDivisor_add
    (Vf : LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual.DvSmallValuationFamily (K := K))
    (X : Example32SmallBase K)
    (x y : (example32RationalFunctionsLiftedULift).obj X) :
    example32AlignedDivisor Vf X (x + y) =
      example32AlignedDivisor Vf X x +
        example32AlignedDivisor Vf X y :=
  map_add _ x y

end LeanFormal.IUT.XiFPaper.S481AlignedDivisorMapActual
end
