import tmp.sheaf.xif.paper.S491AlignedDivisorMapActual
import tmp.sheaf.xif.paper.S468DivisorNaturalityActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S583AlignedDivisorEvalS491Actual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
open LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual
open Iut.SourceFinitePlaceReconstruction
open Additive

universe u
variable {K : Type u} [Field K]

theorem example32DivisorAlignedS491_eval
    (V : LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual.DvSmallValuationFamily (K := K))
    (X : Example32SmallBase K) (u : (coverField X)ˣ) :
    example32DivisorAlignedS491 (K := K) V X
        (Additive.ofMul (ULift.up u)) =
      grothendieckStageDivisorULift'
        (divisorMap (K := K) (L := coverField X) (V X) (Additive.ofMul u)) := by
  rfl

theorem grothendieckStageDivisorULift'_of
    (x : StageDivisor.{u}) :
    grothendieckStageDivisorULift'
        (Algebra.GrothendieckAddGroup.of x) =
      Algebra.GrothendieckAddGroup.of
        (stageDivisorULiftEquiv' x) := by
  let map := Algebra.GrothendieckAddGroup.of.comp
    (stageDivisorULiftEquiv'.toAddMonoidHom)
  change (Algebra.GrothendieckAddGroup.lift map)
    (Algebra.GrothendieckAddGroup.of x) = map x
  change ((Algebra.GrothendieckAddGroup.lift map).comp
    Algebra.GrothendieckAddGroup.of) x = map x
  rw [← Algebra.GrothendieckAddGroup.lift_symm_apply]
  exact DFunLike.congr_fun
    (Equiv.symm_apply_apply Algebra.GrothendieckAddGroup.lift map) x

theorem stageDivisorULiftEquiv'_ulift_up (n : ℕ) :
    stageDivisorULiftEquiv'
        (ULift.up n : StageDivisor.{u}) =
      (ULift.up n : StageDivisor.{u+1}) := by
  ext
  simp [stageDivisorULiftEquiv', stageDivisorEquivNat]

end LeanFormal.IUT.XiFPaper.S583AlignedDivisorEvalS491Actual

end
