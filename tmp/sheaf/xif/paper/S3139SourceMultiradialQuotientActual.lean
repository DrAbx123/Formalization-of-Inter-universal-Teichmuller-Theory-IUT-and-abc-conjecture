import tmp.sheaf.xif.paper.S3138SourceStepXIActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: actual partial multiradial-representation quotient carrier

The multiradial representation of IUT III, Theorem 3.11(i), on the carrier
level, is the actual source choice data quotiented by the (Ind1)/(Ind2)
indeterminacies, with (Ind3) entering as an upper-semi inequality
(Proposition 3.9(ii); Formalization of IUT (2026-04) §4 :505-524, :602-610).

This file constructs that quotient carrier from the actual source core and
profile of `S3138SourceStepXIActual` using the production
`MultiradialKernel.Core.GeneratedQuotient` and the production profile descent
lemmas (`Profile.logVolume_respects_generated`,
`Profile.quotientPossibleImage`):

* quotient map, descended log-volume, descended possible image, descended
  level readout;
* (Ind1)/(Ind2) invariance of the quotient map from the actual inverse laws;
* (Ind3) upper-semi on the quotient possible image;
* (Ind3) level increase and log-volume monotonicity;
* inhabitedness from the actual source base choice.

Still exact-Missing (referenced, not constructed): the first-triangle
algorithmic mutation BPS -> this quotient target
(`SourceMultiradialMutationDemand` of `S3139StageOneSeamsActual`,
Formalization :505-513).  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.MultiradialKernel.Core
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionProfileActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCarrierActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. The quotient carrier and its descended readouts -/

/-- The partial multiradial representation carrier: the generated
(Ind1)+(Ind2) quotient of the actual source carrier core. -/
abbrev SourceMultiradialCarrier (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Type ui :=
  (sourceStepXICore I).GeneratedQuotient

/-- The quotient map: the radial readout of a source choice. -/
def sourceMultiradialMap (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceStepXIChoice I → SourceMultiradialCarrier I :=
  Core.generatedQuotientMap (sourceStepXICore I)

/-- The log-volume readout descended to the quotient ((Ind1)/(Ind2)-invariant
by `Profile.logVolume_respects_generated`). -/
noncomputable def sourceMultiradialLogVolume
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceMultiradialCarrier I → ℝ :=
  Quotient.lift (sourceStepXIProfile I).logVolume
    (fun a b h => (sourceStepXIProfile I).logVolume_respects_generated h)

/-- The possible-image readout descended to the quotient (production
`Profile.quotientPossibleImage`). -/
def sourceMultiradialPossibleImage
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceMultiradialCarrier I → Set ℝ :=
  (sourceStepXIProfile I).quotientPossibleImage

/-- The level readout descended to the quotient ((Ind1)/(Ind2) preserve the
level by `Core.generatedRelation_level_eq`). -/
def sourceMultiradialLevel (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    SourceMultiradialCarrier I → ℕ :=
  Quotient.lift (sourceStepXICore I).level
    (fun a b h => Core.generatedRelation_level_eq (sourceStepXICore I) h)

@[simp] theorem sourceMultiradialLogVolume_mk
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c : SourceStepXIChoice I) :
    sourceMultiradialLogVolume I (sourceMultiradialMap I c) =
      (sourceStepXIProfile I).logVolume c := rfl

@[simp] theorem sourceMultiradialLevel_mk
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c : SourceStepXIChoice I) :
    sourceMultiradialLevel I (sourceMultiradialMap I c) = c.2 := rfl

/-- The descended possible image is the profile possible image on the image of
the quotient map. -/
theorem sourceMultiradialPossibleImage_mk
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (c : SourceStepXIChoice I) :
    sourceMultiradialPossibleImage I (sourceMultiradialMap I c) =
      (sourceStepXIProfile I).possibleImage c :=
  (sourceStepXIProfile I).quotientPossibleImage_mk c

theorem sourceMultiradialPossibleImage_nonempty
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (q : SourceMultiradialCarrier I) :
    (sourceMultiradialPossibleImage I q).Nonempty :=
  (sourceStepXIProfile I).quotientPossibleImage_nonempty q

/-- (Ind3) upper-semi on the quotient: advancing the actual vertical direction
can only increase the possible log-volumes. -/
theorem sourceMultiradialPossibleImage_ind3_upper
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Nat)
    (c : SourceStepXIChoice I) (z : ℝ)
    (hz : z ∈ sourceMultiradialPossibleImage I (sourceMultiradialMap I c)) :
    ∃ w, w ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3 n c)) ∧ z ≤ w :=
  (sourceStepXIProfile I).quotientPossibleImage_ind3_upper c n z hz

/-! ## 2. (Ind1)/(Ind2) invariance and (Ind3) monotonicity -/

/-- (Ind1) acts trivially on the quotient. -/
theorem sourceMultiradialMap_ind1
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (g : SourceStepXILabel) (c : SourceStepXIChoice I) :
    sourceMultiradialMap I ((sourceStepXICore I).ind1 g c) =
      sourceMultiradialMap I c :=
  Core.generatedQuotientMap_eq_of_generated (sourceStepXICore I)
    (GeneratedEqualityRelation.ind1
      ⟨-g, (sourceStepXICore I).ind1_inverse g c⟩)

/-- (Ind2) acts trivially on the quotient. -/
theorem sourceMultiradialMap_ind2
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (g : SourceStepXILabel) (c : SourceStepXIChoice I) :
    sourceMultiradialMap I ((sourceStepXICore I).ind2 g c) =
      sourceMultiradialMap I c :=
  Core.generatedQuotientMap_eq_of_generated (sourceStepXICore I)
    (GeneratedEqualityRelation.ind2
      ⟨-g, (sourceStepXICore I).ind2_inverse g c⟩)

/-- The descended log-volume is monotone under the actual (Ind3) direction. -/
theorem sourceMultiradialLogVolume_ind3_le
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Nat)
    (c : SourceStepXIChoice I) :
    sourceMultiradialLogVolume I (sourceMultiradialMap I c) ≤
      sourceMultiradialLogVolume I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3 n c)) :=
  (sourceStepXIProfile I).ind3_upper n c

/-- The level is well-defined on the quotient and increases by `n` under the
actual (Ind3) direction. -/
theorem sourceMultiradialLevel_ind3
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Nat)
    (c : SourceStepXIChoice I) :
    sourceMultiradialLevel I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3 n c)) =
      sourceMultiradialLevel I (sourceMultiradialMap I c) + n :=
  (sourceStepXICarrier I).ind3_level_eq n c

/-- The quotient carrier is inhabited by the actual source base choice. -/
theorem sourceMultiradialCarrier_nonempty
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Nonempty (SourceMultiradialCarrier I) :=
  ⟨sourceMultiradialMap I (SourceStepXIBase I)⟩

end LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual

end
