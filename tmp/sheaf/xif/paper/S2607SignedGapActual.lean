import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2607SignedGapActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

noncomputable def SignedVolume (S : Set (I.ThetaPilotPoint v)) : ENNReal :=
  ⨆ y ∈ S, ENNReal.ofReal (- I.sourceLocalLogDegree v y)

theorem SignedVolume_singleton (y : I.ThetaPilotPoint v) :
    SignedVolume I v {y} = ENNReal.ofReal (- I.sourceLocalLogDegree v y) := by
  unfold SignedVolume
  refine le_antisymm ?_ ?_
  · refine iSup_le fun z => iSup_le fun hz => ?_
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
  · exact le_iSup_of_le y (le_iSup_of_le (Set.mem_singleton y) le_rfl)

/-- Signed gap 1: hval + weight <= signed volume -> height <= (1+eps)*signed
volume + A. -/
theorem signedGap1_height
    (j : SignedLabel l.value)
    {eps A : Real} (heps : 0 <= eps) (hA : 0 <= A)
    (hval : forall a b c : Nat, IsABCTriple a b c ->
      forall p, p ∈ arithmeticPrimeSupport (abcRationalPoint a c) ->
        max 0 (-(padicValRat p (abcRationalPoint a c) : Real)) <= 1 + eps)
    (hweight : forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        (SignedVolume I v
          {I.sourceThetaPilotPoint v R n j}).toReal)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    Height.logHeight₁ (abcRationalPoint a c) <=
      (1 + eps) *
        (SignedVolume I v {I.sourceThetaPilotPoint v R n j}).toReal + A := by
  have hheight : Height.logHeight₁ (abcRationalPoint a c) <=
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) :=
    abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound
      habc heps (hval a b c habc)
  have hw := hweight a b c habc
  nlinarith [hheight, hw, heps, hA]

/-- Signed gap 2 target: split + unit + point finiteness data give
signedRegionVolume <= (1+eps)*weight + signedHull + D. -/
def SignedGap2Target (S : Set (I.ThetaPilotPoint v)) (j : SignedLabel l.value)
    (eps D0 D1 : Real) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    (SignedVolume I v (S ∪ {I.sourceThetaPilotPoint v R n j})).toReal <=
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
        (SignedVolume I v S).toReal + D0 + D1

#print axioms SignedVolume_singleton
#print axioms signedGap1_height

end LeanFormal.IUT.XiFPaper.S2607SignedGapActual
end
