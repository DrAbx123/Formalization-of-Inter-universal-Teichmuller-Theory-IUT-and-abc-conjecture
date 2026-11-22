import tmp.sheaf.xif.paper.MultiradialProcessionActual
import tmp.sheaf.xif.paper.S3139SourceMultiradialQuotientActual
import tmp.sheaf.xif.paper.S3139SourceMultiradialConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.defProp false

/-!
# S3139: Ind1/Ind2/Ind3 action laws on the actual multiradial core (vendor-adapted)

Adapted from vendor promachina Iut/Stage1/IUTStage1Theorem311.lean Ind-action
laws: ind1_preserves_procession_column:251, ind2_preserves_directSummandCount:258,
ind3_preserves_logThetaColumn:266, ind3_preserves_logVolumeCompatibility:290,
ind3_target_logVolumeCompatible:298, ind3_target_logVolumeUpperBound:305.
Re-proved on our actual core: the (Ind1)/(Ind2) stability of the descended
multiradial map and the (Ind3) one-sided upper-semi relation.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139VendorIndActionLawsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialConsumerActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- The actual Ind1/Ind2/Ind3 action laws on the multiradial core (vendor
action-law schema). -/
structure SourceIndActionLaws
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- (Ind1) stability of the descended multiradial map (vendor ind1 columns). -/
  ind1_stable : ∀ (g : SourceStepXILabel) (c : SourceStepXIChoice J),
    sourceMultiradialMap J ((sourceStepXICore J).ind1 g c) = sourceMultiradialMap J c
  /-- (Ind2) stability of the descended multiradial map (vendor ind2 summands). -/
  ind2_stable : ∀ (g : SourceStepXILabel) (c : SourceStepXIChoice J),
    sourceMultiradialMap J ((sourceStepXICore J).ind2 g c) = sourceMultiradialMap J c
  /-- (Ind3) one-sided upper-semi relation on the descended possible volumes. -/
  ind3_upper : ∀ (n : Nat) (c : SourceStepXIChoice J) (z : ℝ),
    z ∈ sourceMultiradialPossibleImage J (sourceMultiradialMap J c) →
      ∃ w, w ∈ sourceMultiradialPossibleImage J
        (sourceMultiradialMap J ((sourceStepXICore J).ind3 n c)) ∧ z ≤ w

/-- The actual Ind1/Ind2/Ind3 action laws hold (constructed from the S3139
multiradial quotient lemmas). -/
noncomputable def sourceIndActionLaws
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceIndActionLaws J where
  ind1_stable := fun g c => sourceMultiradialMap_ind1 J g c
  ind2_stable := fun g c => sourceMultiradialMap_ind2 J g c
  ind3_upper := fun n c z hz => sourceMultiradialPossibleImage_ind3_upper J n c z hz

end LeanFormal.IUT.XiFPaper.S3139VendorIndActionLawsActual

end
