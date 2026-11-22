import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction

/-! # S1164: operation-arrow realization / exact first gap

Candidate concrete four arrows are built from the actual source f-prime-strips
and source links I.fPrimeStripAt / I.fLinkAt at lattice points
  bottomEnv = (0,0), bottomGau = (0,1),
  topEnv    = (1,0), topGau    = (1,1).
The candidate commEnv square is actually proved from fLinkAt_trans.
This is NOT yet the actual evaluation of a SourceRun: the provenance that the
candidate upperEnv is produced by the run's actual operation remains the exact
first gap. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1164OperationArrowActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Candidate lowerEnv: bottomEnv (0,0) -> bottomGau (0,1). -/
noncomputable def s1164LowerEnv :
    FPrimeStripEquiv (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 0 1) :=
  I.fLinkAt 0 0 0 1

/-- Candidate verticalEnv: bottomEnv (0,0) -> topEnv (1,0). -/
noncomputable def s1164VerticalEnv :
    FPrimeStripEquiv (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 1 0) :=
  I.fLinkAt 0 0 1 0

/-- Candidate verticalGau: bottomGau (0,1) -> topGau (1,1). -/
noncomputable def s1164VerticalGau :
    FPrimeStripEquiv (I.fPrimeStripAt 0 1) (I.fPrimeStripAt 1 1) :=
  I.fLinkAt 0 1 1 1

/-- Candidate upperEnv: topEnv (1,0) -> topGau (1,1). -/
noncomputable def s1164UpperEnv :
    FPrimeStripEquiv (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1) :=
  I.fLinkAt 1 0 1 1

/-- Candidate commEnv square, actual from source-link transitivity. -/
theorem s1164CommEnv :
    FPrimeStripEquiv.trans (s1164LowerEnv I) (s1164VerticalGau I) =
      FPrimeStripEquiv.trans (s1164VerticalEnv I) (s1164UpperEnv I) := by
  unfold s1164LowerEnv s1164VerticalGau s1164VerticalEnv s1164UpperEnv
  rw [I.fLinkAt_trans, I.fLinkAt_trans]

/-- Four candidate arrows and the commEnv square. -/
structure S1164OperationArrows where
  lowerEnv : FPrimeStripEquiv (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 0 1)
  verticalEnv : FPrimeStripEquiv (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 1 0)
  verticalGau : FPrimeStripEquiv (I.fPrimeStripAt 0 1) (I.fPrimeStripAt 1 1)
  upperEnv : FPrimeStripEquiv (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1)
  commEnv :
    FPrimeStripEquiv.trans lowerEnv verticalGau =
      FPrimeStripEquiv.trans verticalEnv upperEnv

/-- Actual candidate operation-arrow package. -/
noncomputable def s1164CandidateArrows : S1164OperationArrows I where
  lowerEnv := s1164LowerEnv I
  verticalEnv := s1164VerticalEnv I
  verticalGau := s1164VerticalGau I
  upperEnv := s1164UpperEnv I
  commEnv := s1164CommEnv I

/-- Exact first-gap data: the actual evaluation arrow of the run and the
provenance that it is produced by the source operation. -/
structure S1164ActualEvaluationArrow where
  arrow : FPrimeStripEquiv (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1)
  fromRunOperation : Prop

/-- Exact first gap: an actual evaluation arrow with provenance, not the
candidate fLinkAt arrow. -/
def S1164ActualEvaluationRequired : Prop :=
  Nonempty (S1164ActualEvaluationArrow I)

/-- S1159 OperationArrowRealization: four arrows from actual run operations,
with the commEnv square.  No inhabitant is asserted. -/
structure S1164OperationArrowRealizationData where
  lowerEnv : FPrimeStripEquiv (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 0 1)
  verticalEnv : FPrimeStripEquiv (I.fPrimeStripAt 0 0) (I.fPrimeStripAt 1 0)
  verticalGau : FPrimeStripEquiv (I.fPrimeStripAt 0 1) (I.fPrimeStripAt 1 1)
  upperEnv : FPrimeStripEquiv (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 1)
  commEnv :
    FPrimeStripEquiv.trans lowerEnv verticalGau =
      FPrimeStripEquiv.trans verticalEnv upperEnv
  lowerEnv_fromRun : Prop
  verticalEnv_fromRun : Prop
  verticalGau_fromRun : Prop
  upperEnv_fromRun : Prop

def S1164OperationArrowRealization : Prop :=
  Nonempty (S1164OperationArrowRealizationData I)


end LeanFormal.IUT.XiFPaper.S1164OperationArrowActual
end
