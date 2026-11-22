import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume
import Mathlib

/-!
# O4 source Q <= Theta direction

Production gives the reverse signed direction
`sourceSignedHullLogVolume <= sourceSignedImageLogVolume` (hull contained in the
image union).  The corpus direction `sourceSignedImageLogVolume <=
`sourceSignedHullLogVolume` is equivalent, under finite hull volume, to the
source identity `sourceHullVolume = sourceSetVolume (possibleThetaPilotImageSet)`
(the via-images normalization).  Production proves only the `>=` half of that
volume identity.  This file gives the exact equivalence and decisive no-go.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

namespace LeanFormal.IUT.N8Closure.O4SourceQHullDirection

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Needed corpus direction: image signed log <= hull signed log. -/
def SourceQHullDirection : Prop :=
  ∀ (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l),
    I.sourceHullVolume v R n < ⊤ →
      I.sourceSignedImageLogVolume v R n ≤ I.sourceSignedHullLogVolume v R n

/-- The exact source identity equivalent to the needed direction: the hull
volume is computed by the possible theta-pilot images. -/
def HullVolumeEqPossibleImageVolume : Prop :=
  ∀ (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l),
    I.sourceHullVolume v R n < ⊤ →
      I.sourceHullVolume v R n =
        I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)

/-- The only half production proves: image volume <= hull volume. -/
def ImageVolumeLeHullVolume : Prop :=
  ∀ (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l),
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) ≤
      I.sourceHullVolume v R n

/-- Production's reverse signed direction (actual). -/
theorem hull_signed_le_image_signed_actual (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) :
    I.sourceSignedHullLogVolume v R n ≤ I.sourceSignedImageLogVolume v R n :=
  I.sourceSignedHullLogVolume_le_sourceSignedImageLogVolume v R n hfin

/-- Production's volume half (actual). -/
theorem imageVolume_le_hullVolume_actual (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) ≤
      I.sourceHullVolume v R n :=
  I.sourceHullVolume_ge_imageVolume v R n

/-- The needed signed direction is exactly the via-images hull-volume equality. -/
theorem sourceQHullDirection_iff_hullVolume_eq :
    SourceQHullDirection (I := I) ↔
      HullVolumeEqPossibleImageVolume (I := I) := by
  constructor
  · intro h v R n hfin
    exact I.sourceHullVolume_eq_imageVolume_of_signedImageComparison v R n hfin
      (h v R n hfin)
  · intro h v R n hfin
    exact I.sourceSignedImageComparison_of_hullVolume_eq_imageVolume v R n
      (h v R n hfin)

/-- Decisive no-go: the needed direction is exactly the missing `<=` half
(hull volume <= possible-image volume) of the hull-volume equality.  Production
only supplies the `>=` half.  The missing source theorem is
`sourceHullVolume <= sourceSetVolume (possibleThetaPilotImageSet)`, equivalently
hull computed by the possible theta-pilot images. -/
def SourceQHullDirectionMissing : Prop := SourceQHullDirection (I := I)

end LeanFormal.IUT.N8Closure.O4SourceQHullDirection
