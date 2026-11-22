import tmp.sheaf.xif.paper.Mzk1P0LQThetaMemActual
import tmp.sheaf.xif.paper.Mzk1P0LRegionNonemptyActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaComponentActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaMemActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LRegionNonemptyActual
open MeasureTheory
universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- Exact norm-instance compatibility required to turn the q component into the
tensor fiber norm: the HeightOneSpectrum completion norm and the
CommonPrimeCompletion norm must agree. -/
structure CommonPrimeNormInstanceCompat where
  /-- explicit transport from the HeightOneSpectrum completion to the common-prime
  (normalized) completion; the two presentations need not be definitionally equal. -/
  toCommonPrime :
    Completion (K := I.initial.arithmetic.Fmod) ((C3LAt I place).place) →
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod)
        (p := (C3LAt I place).p) ((C3LAt I place).place)
  norm_eq :
    ∀ x : Completion (K := I.initial.arithmetic.Fmod) ((C3LAt I place).place),
      ‖x‖ = ‖toCommonPrime x‖
def CommonPrimeNormInstanceCompatRequired : Prop :=
  Nonempty (CommonPrimeNormInstanceCompat I place)

theorem tensorUnit_mem_thetaRegion_conditional
    (h : qComponentMemGap I place) :
    (↑(C3LAt I place).tensorUnit : C3LogShellTensorBlockL (C3LAt I place)) ∈
      actualC3LogShellTensorRegionL (C3LAt I place) :=
  tensorUnit_mem_thetaRegion_of_qComponentMem I place h

theorem thetaRegion_nonempty_actual :
    (actualC3LogShellTensorRegionL (C3LAt I place)).Nonempty :=
  thetaRegion_nonempty I place

#print axioms tensorUnit_mem_thetaRegion_conditional
#print axioms thetaRegion_nonempty_actual

end LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaComponentActual
