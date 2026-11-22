import tmp.sheaf.xif.paper.S2595P4WiringActual
import tmp.sheaf.xif.paper.S2593P4CandidateActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S2593P4CandidateActual
open LeanFormal.IUT.XiFPaper.S2595P4WiringActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2596P4ScalingCorrectionActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)
variable (T : SourceNativeInitialThetaData l)
variable (β : Bad (nativePlaceSelection T))

/-- The exact scaling-degree correction needed to pass from the unscaled
S2593 dictionary to the frozen scaled dictionary: the `D.scaling` factor has
zero source local log-degree.  `SourceUnitRegionHaarData` only supplies
`<= 0`, not `= 0`, so this is an additional datum/consequence to be proved. -/
def P4ScalingDegreeCorrection : Prop :=
  I.sourceLocalLogDegree v D.scaling = 0

/-- Scaling degree zero is exactly what makes the scaled candidate log-degree
equal the unscaled candidate log-degree. -/
theorem P4_scaled_candidate_logDegree
    (hcorr : P4ScalingDegreeCorrection I v R n D) (a b c : Nat) :
    I.sourceLocalLogDegree v
        (D.scaling * P4CandidatePoint I R T β a b c) =
      I.sourceLocalLogDegree v (P4CandidatePoint I R T β a b c) := by
  rw [I.sourceLocalLogDegree_mul v D.scaling (P4CandidatePoint I R T β a b c)]
  rw [show I.sourceLocalLogDegree v D.scaling = 0 from hcorr]
  exact zero_add _

/-- If the unit-region scaling is literally `1`, the correction holds. -/
theorem P4ScalingDegreeCorrection_of_scaling_eq_one
    (h : D.scaling = 1) :
    P4ScalingDegreeCorrection I v R n D := by
  rw [P4ScalingDegreeCorrection, h, I.sourceLocalLogDegree_one]

/-- **P4 scaling correction, actual**: the unscaled S2593 dictionary plus
zero scaling degree gives the frozen scaled candidate dictionary. -/
theorem P4ScaledCandidateDictionary_of_source
    (hcorr : P4ScalingDegreeCorrection I v R n D)
    (h : P4SourceLogDegreeDictionary I R T β) :
    P4ScaledCandidateDictionary I v R n D T β := by
  intro a b c habc
  have hh := h a b c habc
  rw [P4_scaled_candidate_logDegree I v R n D T β hcorr a b c]
  exact hh

/-- The corrected wiring: unscaled S2593 dictionary + scaling correction
gives the actual `hweightvol` at the value-realized carrier. -/
theorem P4_hweightvol_of_sourceDictionary_corrected
    (hcorr : P4ScalingDegreeCorrection I v R n D)
    (h : P4SourceLogDegreeDictionary I R T β) :
    forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        ((I.sourceUnitRegionHaarInterface v R n D).logVolume
          (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D)
            (fun a b c => P4CandidatePoint I R T β a b c) a b c)).toReal :=
  P4_hweightvol_of_scaledCandidate I v R n D T β
    (P4ScaledCandidateDictionary_of_source I v R n D T β hcorr h)

#print axioms P4ScalingDegreeCorrection_of_scaling_eq_one
#print axioms P4ScaledCandidateDictionary_of_source
#print axioms P4_scaled_candidate_logDegree
#print axioms P4_hweightvol_of_sourceDictionary_corrected

end LeanFormal.IUT.XiFPaper.S2596P4ScalingCorrectionActual
end
