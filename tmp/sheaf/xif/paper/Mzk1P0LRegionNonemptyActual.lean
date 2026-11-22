import tmp.sheaf.xif.paper.Mzk1P0LIndexNonemptyActual
import tmp.sheaf.xif.paper.Mzk1P0LRegionPosActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorIntegralRegion
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LRegionNonemptyActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LIndexNonemptyActual
open MeasureTheory
universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem zero_mem_thetaRegion :
    (0 : C3LogShellTensorBlockL (C3LAt I place)) ∈
      actualC3LogShellTensorRegionL (C3LAt I place) := by
  letI : Nonempty (C3LAt I place).tensorIndex := tensorIndex_nonempty I place
  unfold actualC3LogShellTensorRegionL
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro i _
    dsimp only
    change (0 : C3LogShellFiberL (C3LAt I place) i) ∈
      actualC3LogShellL (C3LAt I place) i
    rw [actualC3LogShellL_eq_integralLogShell]
    exact (integralLogShell (K := C3LogShellFiberL (C3LAt I place) i)
      (p := (C3LAt I place).p)).zero_mem
  · show (finitePadicTensorTprod (p := (C3LAt I place).p)
        (M := fun i => C3LogShellFiberL (C3LAt I place) i)
        (0 : (i : (C3LAt I place).tensorIndex) → C3LogShellFiberL (C3LAt I place) i)) = 0
    exact MultilinearMap.map_zero
      (f := finitePadicTensorTprod (p := (C3LAt I place).p)
        (M := fun i => C3LogShellFiberL (C3LAt I place) i))
theorem thetaRegion_nonempty :
    (actualC3LogShellTensorRegionL (C3LAt I place)).Nonempty :=
  ⟨0, zero_mem_thetaRegion I place⟩
end LeanFormal.IUT.XiFPaper.Mzk1P0LRegionNonemptyActual