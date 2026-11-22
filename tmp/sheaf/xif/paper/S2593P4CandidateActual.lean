import tmp.sheaf.xif.paper.S2592ValueMapCandidateActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import tmp.sheaf.xif.paper.S2591PointLocalLogDegreeActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2591PointLocalLogDegreeActual
open LeanFormal.IUT.XiFPaper.S2592ValueMapCandidateActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2593P4CandidateActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {v : V} (R : I.SourceImageRealization v)
variable (T : SourceNativeInitialThetaData.{0} l)
variable (β : Bad (nativePlaceSelection T))

/-- The candidate value-map point attached to `(a,n,c)`: the tensor-block point
`S2588PointMap a n c` transported to the source theta-pilot carrier by
`S2592TensorToThetaPilotPoint`. -/
noncomputable def P4CandidatePoint :
    Nat -> Nat -> Nat -> I.ThetaPilotPoint v :=
  fun a n c => S2592TensorToThetaPilotPoint I R (S2588PointMap T β a n c)

/-- The candidate source local log-degree of the point. -/
noncomputable def P4SourceLogDegreeCandidate :
    Nat -> Nat -> Nat -> Real :=
  fun a n c => I.sourceLocalLogDegree v (P4CandidatePoint I R T β a n c)

/-- Under pointwise degree faithfulness, the candidate equals the cardinality
of `SourceVolumeIndex` times the log of the tensor norm. -/
theorem P4SourceLogDegreeCandidate_eq (hdeg :
    forall x : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd x)) = x) :
    forall a n c : Nat,
      P4SourceLogDegreeCandidate I R T β a n c =
        (Fintype.card (Theorem311Source.OriginalInput.SourceVolumeIndex l) : Real) *
          Real.log ‖S2588PointMap T β a n c‖ := by
  intro a n c
  unfold P4SourceLogDegreeCandidate P4CandidatePoint
  have hconst : S2592TensorToThetaPilotPoint I R (S2588PointMap T β a n c) =
      I.constantThetaPilotPoint v R
        (Multiplicative.ofAdd (Real.log ‖S2588PointMap T β a n c‖)) := rfl
  rw [hconst]
  exact I.sourceLocalLogDegree_constant v R _ hdeg

/-- The corrected P4 dictionary with the `S2592` candidate point:
`arithmeticWeight x <= sourceLocalLogDegree(candidate point)`. -/
def P4SourceLogDegreeDictionary : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    arithmeticWeight (abcRationalPoint a c) <=
      P4SourceLogDegreeCandidate I R T β a b c

/-- The minimal inequality equivalent to the candidate dictionary, under
pointwise degree faithfulness. -/
theorem P4SourceLogDegreeDictionary_iff_minimal (hdeg :
    forall x : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd x)) = x) :
    P4SourceLogDegreeDictionary I R T β <->
      forall a b c : Nat, IsABCTriple a b c ->
        arithmeticWeight (abcRationalPoint a c) <=
          (Fintype.card (Theorem311Source.OriginalInput.SourceVolumeIndex l) : Real) *
            Real.log ‖S2588PointMap T β a b c‖ := by
  constructor
  · intro h a b c habc
    have hh := h a b c habc
    rw [P4SourceLogDegreeCandidate_eq I R T β hdeg a b c] at hh
    exact hh
  · intro h a b c habc
    have hh := h a b c habc
    rw [P4SourceLogDegreeCandidate_eq I R T β hdeg a b c]
    exact hh

#print axioms P4SourceLogDegreeCandidate_eq
#print axioms P4SourceLogDegreeDictionary_iff_minimal

end LeanFormal.IUT.XiFPaper.S2593P4CandidateActual
end
