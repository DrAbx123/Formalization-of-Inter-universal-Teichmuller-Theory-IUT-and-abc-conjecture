import tmp.sheaf.xif.paper.S412DvTriangleTauActual
import Iut.Foundations.SourceFiniteStageModelFrobenioid

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S457DivisorMapActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual
open Iut.SourceFinitePlaceReconstruction
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual
open Additive

universe u

variable {K : Type u} [Field K]
variable {L : Type u} [Field L] [Algebra K L]
variable (V : DvCoverNormalizedValuationData K L)

/-- Valuation exponent as an additive hom from Additive L^× to Z. -/
noncomputable def valuationExponentHom :
    Additive Lˣ →+ ℤ where
  toFun x := Multiplicative.toAdd (V.valuation x.toMul)
  map_zero' := by simp
  map_add' x y := by simp [map_mul]

/-- Divisor map to the Grothendieck group of the stage divisor monoid. -/
noncomputable def divisorMap :
    Additive Lˣ →+ Algebra.GrothendieckAddGroup StageDivisor.{u} :=
  intToStageDivisorGrothendieck.comp (valuationExponentHom V)

theorem divisorMap_add (x y : Additive Lˣ) :
    divisorMap V (x + y) = divisorMap V x + divisorMap V y := by
  exact map_add (divisorMap V) x y

theorem divisorMap_apply (x : Additive Lˣ) :
    divisorMap V x =
      intToStageDivisorGrothendieck (Multiplicative.toAdd (V.valuation x.toMul)) := by
  rfl

/-- Family version: for each cover L with given valuation data, the divisor map. -/
noncomputable def divisorMapFamily
    (Vf : ∀ (L : DvTriangleFieldCover K) [Field L.obj.obj] [Algebra K L.obj.obj],
      DvCoverNormalizedValuationData K L.obj.obj)
    (L : DvTriangleFieldCover K) [Field L.obj.obj] [Algebra K L.obj.obj] :
    Additive L.obj.objˣ →+ Algebra.GrothendieckAddGroup StageDivisor.{u} :=
  divisorMap (Vf L)

end LeanFormal.IUT.XiFPaper.S457DivisorMapActual

end
