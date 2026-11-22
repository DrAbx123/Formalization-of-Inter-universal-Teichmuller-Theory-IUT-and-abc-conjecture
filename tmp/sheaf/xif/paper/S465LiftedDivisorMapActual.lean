import tmp.sheaf.xif.paper.S457DivisorMapActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual
open Iut.SourceFinitePlaceReconstruction
open Additive

universe u

variable {K : Type u} [Field K]
variable {L : Type u} [Field L] [Algebra K L]
variable (V : DvCoverNormalizedValuationData K L)

/-- The ULift-down map Additive (ULift L^x) ->+ Additive L^x. -/
noncomputable def uliftAdditiveDown :
    Additive (ULift.{u + 1} Lˣ) →+ Additive Lˣ where
  toFun x := Additive.ofMul x.toMul.down
  map_zero' := rfl
  map_add' x y := rfl

/-- Lifted divisor map at universe u+1, using the S457 map after ULift down. -/
noncomputable def liftedDivisorMap :
    Additive (ULift.{u + 1} Lˣ) →+
      Algebra.GrothendieckAddGroup StageDivisor.{u} :=
  (divisorMap (K := K) (L := L) V).comp (uliftAdditiveDown (L := L))

theorem liftedDivisorMap_apply (x : Additive (ULift.{u + 1} Lˣ)) :
    liftedDivisorMap V x = divisorMap V (Additive.ofMul x.toMul.down) := by
  rfl

theorem liftedDivisorMap_add (x y : Additive (ULift.{u + 1} Lˣ)) :
    liftedDivisorMap V (x + y) =
      liftedDivisorMap V x + liftedDivisorMap V y := by
  exact map_add (liftedDivisorMap V) x y

/-- Family version at universe u+1, conditional on a valuation family. -/
noncomputable def liftedDivisorMapFamily
    (Vf : ∀ (L : DvTriangleFieldCover K) [Field L.obj.obj] [Algebra K L.obj.obj],
      DvCoverNormalizedValuationData K L.obj.obj)
    (L : DvTriangleFieldCover K) [Field L.obj.obj] [Algebra K L.obj.obj] :
    Additive (ULift.{u + 1} L.obj.objˣ) →+
      Algebra.GrothendieckAddGroup StageDivisor.{u} :=
  liftedDivisorMap (Vf L)

end LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual

end
