import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HunitEpsilonTransferReduction

/-! # Stage-4 host: instantiation attempt of the prior-art hunit/unit-region supplies

PRIOR ART (§7.9, checked first): SourceUnitRegionHaarDataActual.lean (:346
sourceHaarActualOriginalInput, :374 sourceHaarActualImageRealization, :416
sourceHaarActualData, :441 scaling); HunitEpsilonTransferReduction.lean (:90
cor312GapSupply_hunit_of_epsilon_hullBound, :103 converse, :118
sourceInterface variant).

WHAT IS ATTEMPTED: instantiate the prior-art epsilon-to-sharp hunit transfer with the
concrete degenerate Haar datum sourceHaarActualData S n.  Its degreeBound is 0 and its
unitRegion is the actual source hull itself, so the comparison is trivial; this is an
HONEST DEGENERATE instantiation, NOT the paper's nondegenerate normalization.  The
prior art records the frozen refutation cor312GapSupply_not_exists_epsilon_hullBound_
of_degreeFaithful (:166): under pointwise degree faithfulness no such datum exists for
the source hull, so no nondegenerate instantiation is claimed.

LABEL: instantiation attempt (degenerate calibration) + exact data.  Registry frozen;
new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136SourceUnitRegionInstantiationAttemptActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{0} l)
variable (n : ThetaPilotCarrier l)

/-- The concrete degenerate Haar datum has degreeBound 0. -/
theorem lgpSourceHaarActualData_degreeBound :
    (sourceHaarActualData (l := l) S n).degreeBound = 0 := rfl

/-- The sharp hunit comparison is trivially satisfied by the degenerate datum. -/
theorem lgpSourceHaarActualData_hunitSharp :
    ENNReal.ofReal (sourceHaarActualData (l := l) S n).degreeBound ≤
      (sourceHaarActualOriginalInput (l := l) S).sourceHullVolume ()
        (sourceHaarActualImageRealization (l := l) S) n + ENNReal.ofReal (0 : ℝ) := by
  rw [lgpSourceHaarActualData_degreeBound]
  simp

/-- Its per-epsilon form via the prior-art converse transfer. -/
theorem lgpSourceHaarActualData_hunitEpsilon :
    ∀ ε : NNReal, 0 < ε →
      ENNReal.ofReal (sourceHaarActualData (l := l) S n).degreeBound ≤
        (sourceHaarActualOriginalInput (l := l) S).sourceHullVolume ()
          (sourceHaarActualImageRealization (l := l) S) n + ENNReal.ofReal (0 : ℝ) +
          (ε : ENNReal) :=
  cor312GapSupply_epsilon_hullBound_of_hunit
    (I := sourceHaarActualOriginalInput (l := l) S) () (sourceHaarActualImageRealization (l := l) S) n
    (sourceHaarActualData (l := l) S n) (D₀ := 0) (by norm_num)
    (lgpSourceHaarActualData_hunitSharp (l := l) S n)

/-- The prior-art epsilon-to-sharp transfer returns the sharp comparison (round trip). -/
theorem lgpSourceHaarActualData_hunitRoundTrip :
    ENNReal.ofReal (sourceHaarActualData (l := l) S n).degreeBound ≤
      (sourceHaarActualOriginalInput (l := l) S).sourceHullVolume ()
        (sourceHaarActualImageRealization (l := l) S) n + ENNReal.ofReal (0 : ℝ) :=
  cor312GapSupply_hunit_of_epsilon_hullBound
    (I := sourceHaarActualOriginalInput (l := l) S) () (sourceHaarActualImageRealization (l := l) S) n
    (sourceHaarActualData (l := l) S n) (D₀ := 0) (by norm_num)
    (lgpSourceHaarActualData_hunitEpsilon (l := l) S n)

#check lgpSourceHaarActualData_degreeBound
#check lgpSourceHaarActualData_hunitSharp
#check lgpSourceHaarActualData_hunitEpsilon
#check lgpSourceHaarActualData_hunitRoundTrip

end LeanFormal.IUT.XiFPaper.S3136SourceUnitRegionInstantiationAttemptActual
end