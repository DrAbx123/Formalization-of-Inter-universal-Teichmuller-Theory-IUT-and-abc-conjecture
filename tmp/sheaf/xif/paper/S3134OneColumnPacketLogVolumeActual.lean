import tmp.sheaf.xif.paper.S3134QParameterThetaScaleActual

/-!
# S3134: actual 1-column theta packet log-volume and procession average

The actual 1-column theta packet of the fourth triangle is the actual
`FiniteThetaPacket` of the `(1,0)` theater stage.  Its log-volume is the sum of
the actual theta log-scales over the signed labels (`FiniteThetaPacket.logVolume`,
`Volume.lean` frozen `hull_average` packet), and the source theta special values
are `scale j = q ^ (gaussExponent j)` (IUT II theta special values; IUT III
Remark 3.1.1, (ii)).

This file computes those actual quantities in terms of the actual q-parameter:

* the actual packet log-volume is a sum of `gaussExponent j * log q` terms;
* the actual procession average of the packet log-volume is
  `(sum of gaussExponents / card) * log q`;
* the actual 1-column readout sum at every procession stage is the same
  actual packet log-volume (vertical log-shift invariance of `S1204`).

These are the actual arithmetic identities behind the Theta-side readout of the
q/Theta simultaneous comparison; the hull log-volume of the paper's Corollary
3.12 is NOT identified with this packet average here (that identification is a
separate source object; see `S3134QThetaComparisonGap`).  No inequality is
judged; no sorry, axiom, `True`, `PUnit`, or toy carrier.  WRITE-ONLY: no
lake/lean.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3134QParameterThetaScaleActual

namespace LeanFormal.IUT.XiFPaper.S3134OneColumnPacketLogVolumeActual

universe u v uv ua upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual 1-column theta packet log-volume. -/
noncomputable def S3134OneColumnPacketLogVolume : ℝ :=
  (J.oneColumnPacket 0).logVolume

/-- The actual packet log-volume as a sum of `gaussExponent j * log q` terms. -/
theorem S3134OneColumnPacketLogVolume_eq_gauss_sum :
    S3134OneColumnPacketLogVolume (J := J) =
      ∑ j : SignedLabel l.value,
        ((gaussExponent j.1).toNat : ℝ) * Real.log (S3134QParameter J) := by
  unfold S3134OneColumnPacketLogVolume
  rw [FiniteThetaPacket.logVolume_eq_sum]
  exact Finset.sum_congr rfl
    (fun j _ => S3134QParameter_log_scale_zero (J := J) j)

/-- The actual packet log-volume is the total Gaussian exponent times the actual
`log q` parameter. -/
theorem S3134OneColumnPacketLogVolume_eq :
    S3134OneColumnPacketLogVolume (J := J) =
      (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : ℝ)) *
        Real.log (S3134QParameter J) := by
  rw [S3134OneColumnPacketLogVolume_eq_gauss_sum]
  rw [← Finset.sum_mul]

/-- The actual procession average of the 1-column packet log-volume: the packet
log-volume divided by the signed-label cardinality. -/
noncomputable def S3134OneColumnAverageLogScale : ℝ :=
  S3134OneColumnPacketLogVolume (J := J) /
    (Fintype.card (SignedLabel l.value) : ℝ)

/-- The actual procession average is the average Gaussian exponent times the
actual `log q` parameter. -/
theorem S3134OneColumnAverageLogScale_eq :
    S3134OneColumnAverageLogScale (J := J) =
      ((∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : ℝ)) /
        (Fintype.card (SignedLabel l.value) : ℝ)) *
        Real.log (S3134QParameter J) := by
  unfold S3134OneColumnAverageLogScale
  rw [S3134OneColumnPacketLogVolume_eq_gauss_sum]
  rw [← Finset.sum_mul]
  ring

/-- The sum of the actual 1-column log readouts at any procession stage is the
actual packet log-volume (vertical log-shift invariance, `S1204`). -/
theorem S3134OneColumnReadout_sum_eq (m : Int) :
    (∑ j : SignedLabel l.value, oneColumnLogReadout J m j) =
      S3134OneColumnPacketLogVolume (J := J) := by
  unfold S3134OneColumnPacketLogVolume
  rw [FiniteThetaPacket.logVolume_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [oneColumnLogReadout_shift J m 0 j]
  rfl

/-- The actual procession average of the 1-column log readouts is the same at
every procession stage. -/
theorem S3134OneColumnReadoutAverage_eq (m : Int) :
    (∑ j : SignedLabel l.value, oneColumnLogReadout J m j) /
        (Fintype.card (SignedLabel l.value) : ℝ) =
      S3134OneColumnAverageLogScale (J := J) := by
  rw [S3134OneColumnReadout_sum_eq]
  rfl

#check S3134OneColumnPacketLogVolume
#check S3134OneColumnPacketLogVolume_eq_gauss_sum
#check S3134OneColumnPacketLogVolume_eq
#check S3134OneColumnAverageLogScale
#check S3134OneColumnAverageLogScale_eq
#check S3134OneColumnReadout_sum_eq
#check S3134OneColumnReadoutAverage_eq

end LeanFormal.IUT.XiFPaper.S3134OneColumnPacketLogVolumeActual
