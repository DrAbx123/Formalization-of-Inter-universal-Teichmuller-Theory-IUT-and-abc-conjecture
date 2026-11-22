import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2725ThetaImageHullActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- Bundled actual theta-pilot image interface: the possible image set is
nonempty and consists of actual source theta-pilot points. -/
theorem S2725_thetaImage_interface :
    (I.possibleThetaPilotImageSet v R n).Nonempty ∧
      (∀ j : SignedLabel l.value,
        I.sourceThetaPilotPoint v R n j ∈ I.possibleThetaPilotImageSet v R n) :=
  ⟨I.possibleThetaPilotImageSet_nonempty v R n,
    fun j => I.sourceThetaPilotPoint_mem v R n j⟩

/-- Bundled actual holomorphic hull interface: it contains the possible theta
image, is the least candidate hull, is idempotent, and is closed under the
actual source scalings. -/
theorem S2725_thetaHull_interface :
    I.possibleThetaPilotImageSet v R n ⊆
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ∧
      CandidateHull (I.sourceScalingUnits v) (I.sourceHolomorphicHull v R n) ∧
      (∀ H : Submonoid (I.ThetaPilotPoint v),
        CandidateHull (I.sourceScalingUnits v) H →
        I.possibleThetaPilotImageSet v R n ⊆ (H : Set (I.ThetaPilotPoint v)) →
        I.sourceHolomorphicHull v R n ≤ H) ∧
      holomorphicHull (I.sourceScalingUnits v)
          (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) =
        I.sourceHolomorphicHull v R n ∧
      (∀ s : I.ThetaPilotPoint v, s ∈ I.sourceScalingUnits v →
        ∀ x : I.ThetaPilotPoint v, x ∈ I.sourceHolomorphicHull v R n →
          s * x ∈ I.sourceHolomorphicHull v R n) :=
  ⟨I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n,
    I.sourceHolomorphicHull_candidate v R n,
    fun H hH hS => I.sourceHolomorphicHull_le v R n hH hS,
    I.sourceHolomorphicHull_idempotent v R n,
    fun s hs x hx => I.sourceHolomorphicHull_scaling_mem v R n hs hx⟩

/-- Every actual theta-pilot image point lies in the actual hull. -/
theorem S2725_thetaPoint_mem_hull
    (j : SignedLabel l.value) :
    I.sourceThetaPilotPoint v R n j ∈ I.sourceHolomorphicHull v R n :=
  I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j

#print axioms S2725_thetaImage_interface
#print axioms S2725_thetaHull_interface
#print axioms S2725_thetaPoint_mem_hull

end LeanFormal.IUT.XiFPaper.S2725ThetaImageHullActual
end
