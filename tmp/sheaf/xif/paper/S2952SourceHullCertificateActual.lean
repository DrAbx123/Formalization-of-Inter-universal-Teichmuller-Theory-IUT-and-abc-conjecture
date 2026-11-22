import tmp.sheaf.xif.paper.S2951ThetaSignedActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2951ThetaSignedActual
open Finset
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2952SourceHullCertificateActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- The source hull finite hull, with hull volume equal to the actual signed
source hull log-volume. -/
noncomputable def S2952SourceFiniteHull :
    FiniteHull (SignedLabel l.value) where
  volume := fun _ => S2951ThetaSigned (I := I) v R n
  hullVolume := S2951ThetaSigned (I := I) v R n
  contains := fun _ => le_rfl

/-- Unit weights carrying the actual signed hull volume. -/
noncomputable def S2952SourceWeightedValues :
    WeightedValues (SignedLabel l.value) where
  value := fun _ => S2951ThetaSigned (I := I) v R n
  weight := fun _ => 1
  weightTotal := Fintype.card (SignedLabel l.value)
  weightTotal_pos :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨zeroSignedLabel (l := l)⟩)
  weightTotal_eq_sum := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- Actual source hull certificate: thetaSigned is the signed hull log-volume,
not a separately assumed upper bound. -/
noncomputable def S2952SourceHullCertificate :
    StepXIFiniteCertificate (SignedLabel l.value) where
  hull := S2952SourceFiniteHull (I := I) v R n
  weighted := S2952SourceWeightedValues (I := I) v R n
  weighted_matches_hull := fun _ => rfl
  weights_nonnegative := fun _ => zero_le_one
  qSigned := S2951ThetaSigned (I := I) v R n - 1
  thetaSigned := S2951ThetaSigned (I := I) v R n
  q_le_hull := by
    change S2951ThetaSigned (I := I) v R n - 1 <= S2951ThetaSigned (I := I) v R n
    linarith
  hull_le_theta := le_rfl
  q_negative := by
    have h := S2951_thetaSigned_nonpos (I := I) v R n
    linarith

theorem S2952_thetaSigned_eq :
    (S2952SourceHullCertificate I v R n).thetaSigned =
      I.sourceSignedHullLogVolume v R n := rfl

theorem S2952_hullVolume_eq :
    (S2952SourceHullCertificate I v R n).hull.hullVolume =
      I.sourceSignedHullLogVolume v R n := rfl

theorem S2952_q_le_theta :
    (S2952SourceHullCertificate I v R n).qSigned <=
      (S2952SourceHullCertificate I v R n).thetaSigned :=
  StepXIFiniteCertificate.q_le_theta _

theorem S2952_thetaSigned_nonpos :
    (S2952SourceHullCertificate I v R n).thetaSigned <= 0 :=
  S2951_thetaSigned_nonpos (I := I) v R n

#check S2952SourceFiniteHull
#check S2952SourceWeightedValues
#check S2952SourceHullCertificate
#check S2952_thetaSigned_eq
#check S2952_hullVolume_eq
#check S2952_q_le_theta
#check S2952_thetaSigned_nonpos
#print axioms S2952SourceHullCertificate
#print axioms S2952_thetaSigned_eq

end LeanFormal.IUT.XiFPaper.S2952SourceHullCertificateActual
end