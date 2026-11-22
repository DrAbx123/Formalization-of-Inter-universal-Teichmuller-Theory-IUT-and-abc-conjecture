import tmp.sheaf.xif.paper.S491AlignedDivisorMapActual
import tmp.sheaf.xif.paper.S583AlignedDivisorEvalS491Actual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S582AlignedDivisorEvalActual
open Iut
open LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual
open Iut.SourceFinitePlaceReconstruction
universe u
theorem grothendieckStageDivisorULift'_of (x : StageDivisor.{u}) :
    grothendieckStageDivisorULift' (Algebra.GrothendieckAddGroup.of x) =
      Algebra.GrothendieckAddGroup.of (stageDivisorULiftEquiv' x) := by
  unfold grothendieckStageDivisorULift'
  let h : StageDivisor.{u} →+ Algebra.GrothendieckAddGroup StageDivisor.{u+1} :=
    Algebra.GrothendieckAddGroup.of.comp (stageDivisorULiftEquiv').toAddMonoidHom
  have hcomp : (Algebra.GrothendieckAddGroup.lift h).comp
      (Algebra.GrothendieckAddGroup.of) = h := by
    have h1 := Algebra.GrothendieckAddGroup.lift_symm_apply (f :=
      Algebra.GrothendieckAddGroup.lift h)
    rw [Equiv.symm_apply_apply] at h1
    exact h1.symm
  have hx := congrFun (congrArg DFunLike.coe hcomp) x
  change (Algebra.GrothendieckAddGroup.lift h) (AddLocalization.mk x 0) =
    AddLocalization.mk (stageDivisorULiftEquiv' x) 0
  exact hx
end LeanFormal.IUT.XiFPaper.S582AlignedDivisorEvalActual
