import tmp.sheaf.xif.paper.S2607SignedGapActual
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantLocalHeight

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2607SignedGapActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2609SignedGap1InputsActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (j : SignedLabel l.value)

/-- **Gap 1 from the H1 additive height/weight bound.**  The version-2
contract `ABCHeightWeightAdditiveBoundV2` (IUT IV Theorem A) plus
`weight <= signedVolume` gives the per-eps signed gap-1 target. -/
theorem signedGap1_of_additiveBound
    (hadd : ABCHeightWeightAdditiveBoundV2)
    (hweight : forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        (SignedVolume I v {I.sourceThetaPilotPoint v R n j}).toReal) :
    forall eps : Real, 0 < eps -> exists A : Real,
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + eps) *
            (SignedVolume I v {I.sourceThetaPilotPoint v R n j}).toReal + A := by
  intro eps heps
  obtain ⟨A, hA⟩ := hadd eps heps
  refine ⟨A, ?_⟩
  intro a b c habc
  have hh := hA a b c habc
  have hw := hweight a b c habc
  have hpos : 0 <= 1 + eps := by linarith
  nlinarith [hh, hw, hpos]

/-- H1 additive sum form: the local valuation sum dominates the height and is
to be compared with the arithmetic weight.  This is definitionally the
height/weight contract after the actual height expansion. -/
def H1AdditiveSumBound : Prop :=
  forall eps : Real, 0 < eps -> exists A : Real,
    forall a b c : Nat, IsABCTriple a b c ->
      (∑ p ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat p (abcRationalPoint a c) : Real)) *
          Real.log (p : Real)) <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A

/-- H1 additive sum bound is exactly the height/weight contract, using the
actual height expansion. -/
theorem H1AdditiveSumBound_iff :
    H1AdditiveSumBound <-> ABCHeightWeightAdditiveBoundV2 := by
  unfold H1AdditiveSumBound ABCHeightWeightAdditiveBoundV2
  constructor
  · intro h eps heps
    obtain ⟨A, hA⟩ := h eps heps
    exact ⟨A, fun a b c habc => by
      rw [abcRationalPoint_logHeight₁_eq_sum_arithmeticPrimeSupport habc]
      exact hA a b c habc⟩
  · intro h eps heps
    obtain ⟨A, hA⟩ := h eps heps
    exact ⟨A, fun a b c habc => by
      rw [← abcRationalPoint_logHeight₁_eq_sum_arithmeticPrimeSupport habc]
      exact hA a b c habc⟩

#print axioms signedGap1_of_additiveBound
#print axioms H1AdditiveSumBound_iff

end LeanFormal.IUT.XiFPaper.S2609SignedGap1InputsActual
end
