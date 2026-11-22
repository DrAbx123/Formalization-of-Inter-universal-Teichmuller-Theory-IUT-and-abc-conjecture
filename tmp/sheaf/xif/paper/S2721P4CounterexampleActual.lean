import tmp.sheaf.xif.paper.S2593P4CandidateActual
import tmp.sheaf.xif.paper.S2593TensorNormActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Bridge.Cor312CarrierRealizationSpec

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2593P4CandidateActual
open LeanFormal.IUT.XiFPaper.S2593P4CandidateActual
open LeanFormal.IUT.XiFPaper.S2593TensorNormActual
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2721P4CounterexampleActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {v : V} (R : I.SourceImageRealization v)
variable (T : SourceNativeInitialThetaData.{0} l)
variable (β : Bad (nativePlaceSelection T))

theorem P4SourceLogDegreeDictionary_false_of_norm_one
    (hdeg : ∀ x : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd x)) = x)
    (hcard : 0 < (Fintype.card (Theorem311Source.OriginalInput.SourceVolumeIndex l) : Real))
    (hnorm : ‖S2588PointMap T β 1 2 3‖ = 1) :
    ¬ P4SourceLogDegreeDictionary I R T β := by
  intro hdict
  have habc : IsABCTriple 1 2 3 :=
    ⟨Nat.one_pos, by norm_num, by norm_num, Nat.coprime_one_left 2⟩
  have hle := hdict 1 2 3 habc
  rw [P4SourceLogDegreeCandidate_eq I R T β hdeg 1 2 3] at hle
  rw [hnorm, Real.log_one] at hle
  have hweight : arithmeticWeight (abcRationalPoint 1 3) = Real.log 6 :=
    cor312CarrierSpec_arithmeticWeight_abcRationalPoint_one_two_three
  rw [hweight] at hle
  have hlog6 : 0 < Real.log (6 : Real) := Real.log_pos (by norm_num)
  have hzero : (Fintype.card (Theorem311Source.OriginalInput.SourceVolumeIndex l) : Real) * 0 = 0 :=
    mul_zero _
  rw [hzero] at hle
  linarith

#check P4SourceLogDegreeDictionary_false_of_norm_one
#print axioms P4SourceLogDegreeDictionary_false_of_norm_one

end LeanFormal.IUT.XiFPaper.S2721P4CounterexampleActual
end
