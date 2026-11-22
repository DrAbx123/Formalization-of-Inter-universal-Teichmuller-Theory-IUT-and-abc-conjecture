import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmOpenMap
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorIntegralRegion
import tmp.sheaf.xif.paper.S1219ConcreteTensorLandingActual
import Mathlib.Tactic

/-!
# P0-L: theta-region membership status

The zero tensor is proved to lie in the actual L tensor log-shell region; the
q-diagonal tensorUnit membership is reduced to an explicit q-membership field.
The first missing arrow is the q component: q.q lives in the HeightOneSpectrum
completion, while the tensor region fiber is the common-prime completion; the
norm-instance paths differ and no carried compatibility theorem exists.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaMemActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
open MeasureTheory

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- Component q-membership: q lies in every actual local log-shell. -/
def qComponentMemGap : Prop :=
  ∀ i : (C3LAt I place).tensorIndex,
    (C3LAt I place).q.q ∈ actualC3LogShellL (C3LAt I place) i

/-- If q lies in every local log-shell then the diagonal tensor unit lies in
the actual tensor region. -/
theorem tensorUnit_mem_thetaRegion_of_qComponentMem
    (hq : qComponentMemGap I place) :
    (↑(C3LAt I place).tensorUnit : C3LogShellTensorBlockL (C3LAt I place)) ∈
      actualC3LogShellTensorRegionL (C3LAt I place) := by
  unfold actualC3LogShellTensorRegionL
  refine ⟨fun _ => (C3LAt I place).q.q, ?_, ?_⟩
  · intro i _
    exact hq i
  · change (C3LAt I place).tensorLanding (C3LAt I place).q.q =
      ↑(C3LAt I place).tensorUnit
    exact (C3LAt I place).tensorLanding_q

#print axioms tensorUnit_mem_thetaRegion_of_qComponentMem

end LeanFormal.IUT.XiFPaper.Mzk1P0LQThetaMemActual
