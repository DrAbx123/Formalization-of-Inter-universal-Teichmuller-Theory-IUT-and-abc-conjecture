import tmp.sheaf.xif.paper.S3136RegionRelativeReconciliationActual
import tmp.sheaf.xif.paper.S3136Gap2AdditiveWiringActual

/-! # Stage-4 host: gap-2 additive wiring in theta form (reconciliation with abc)

PRIOR ART (§7.9, checked first): S3136Gap2AdditiveWiringActual.lgpGap2_of_additive (ours,
wired from Cor312ComparisonGapReduction:306 + GapDictionaryLayer:372 + Hunit:118);
S3135RegionRelativeIQActual:14 abc's theta W-form; Cor312ComparisonGapReduction:306
consumed hypotheses recorded in S3136RegionRelativeReconciliationActual.

WHAT IS PROVED: the wired gap-2 conclusion expressed in the A26 obligation form and,
given the residual weight <= theta input (abc's exact remaining hypothesis), in theta
form.  Named inputs unchanged: additive height bound, degree/height comparison, point
membership, weight <= theta.  No discharge claim.

LABEL: conditional wiring (theta form). Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136Gap2AdditiveThetaFormActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3136Gap2AdditiveWiringActual
open LeanFormal.IUT.XiFPaper.S3136RegionRelativeReconciliationActual

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{0} l)
variable (n : ThetaPilotCarrier l)

/-- The wired gap-2 conclusion as the A26 obligation form. -/
theorem lgpGap2Additive_obligation
    (p : Nat → Nat → Nat → (sourceHaarActualOriginalInput (l := l) S).ThetaPilotPoint ())
    {eps A : ℝ} (heps : 0 ≤ eps)
    (hmem : ∀ a b c : Nat, IsABCTriple a b c →
      p a b c ∈ (lgpSourceInterface (l := l) S n).unitRegion)
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (hline : ∀ a b c : Nat, IsABCTriple a b c →
      (sourceHaarActualOriginalInput (l := l) S).sourceLocalLogDegree ()
        ((sourceHaarActualData (l := l) S n).scaling * p a b c) ≤
        Height.logHeight₁ (abcRationalPoint a c)) :
    ∃ D : ℝ, LGPRegionVolumeObligation (W := lgpSourceInterface (l := l) S n) p eps D := by
  obtain ⟨D, hD⟩ := lgpGap2_of_additive (l := l) S n p heps hmem hadd hline
  exact ⟨D, fun a b c habc => hD a b c habc⟩

/-- The same conclusion in theta form, given abc's residual weight <= theta input. -/
theorem lgpGap2Additive_theta
    (p : Nat → Nat → Nat → (sourceHaarActualOriginalInput (l := l) S).ThetaPilotPoint ())
    {eps A : ℝ} (heps : 0 ≤ eps)
    (hmem : ∀ a b c : Nat, IsABCTriple a b c →
      p a b c ∈ (lgpSourceInterface (l := l) S n).unitRegion)
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (hline : ∀ a b c : Nat, IsABCTriple a b c →
      (sourceHaarActualOriginalInput (l := l) S).sourceLocalLogDegree ()
        ((sourceHaarActualData (l := l) S n).scaling * p a b c) ≤
        Height.logHeight₁ (abcRationalPoint a c))
    (theta : ℝ)
    (hweightθ : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤ theta) :
    ∃ D : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
      ((lgpSourceInterface (l := l) S n).logVolume
        (normalizedComparisonRegion (lgpSourceInterface (l := l) S n) p a b c)).toReal ≤
        (1 + eps) * theta +
          ((lgpSourceInterface (l := l) S n).logVolume
            (lgpSourceInterface (l := l) S n).hull).toReal + D := by
  obtain ⟨D, hob⟩ := lgpGap2Additive_obligation (l := l) S n p heps hmem hadd hline
  exact ⟨D, lgpRegionVolumeObligation_theta_form (W := lgpSourceInterface (l := l) S n)
    (p := p) heps theta hob hweightθ⟩

#check lgpGap2Additive_obligation
#check lgpGap2Additive_theta

end LeanFormal.IUT.XiFPaper.S3136Gap2AdditiveThetaFormActual
end