import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual
import tmp.sheaf.xif.paper.ProcessionThetaPacketAverageActual
import tmp.sheaf.xif.paper.PaperThetaMagnitudeComparisonProof
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceEtaleThetaTheory

/-!
# Signed magnitude comparison: exact arithmetic condition

Target (PaperThetaMagnitudeSignedActual):

  SignedThetaAverageLeQMagnitude D :=
    (c3ThetaSignedProcession (actualSignedC3 D)).average
      <= paperQPilotLogMagnitude (actualSignedC3 D).

For the source-theater C3, the signed procession values are
  -log((sourceTheater l).thetaPacket.scale j) = (gaussExponent j) * log 5,
so its average is exactly

  SignedThetaAverageCandidate l
    := log 5 * (sum_j (gaussExponent j) / card(SignedLabel l.value)).

This file proves:

* the actual signed average formula equals SignedThetaAverageCandidate l;
* the target follows from the exact real bound
  SignedThetaAverageCandidate l <= paperQPilotLogMagnitude (actualSignedC3 D);
* for l = 5, the target follows from qNorm <= 1/25 together with the exact
  arithmetic identity SignedThetaAverageCandidate 5 = 2 * log 5.

The identity SignedThetaAverageCandidate 5 = 2 * log 5 is kept as the exact
arithmetic comparison FiveGaussExponentAverageIdentity; it follows from the
finite computation sum gaussExponent over SignedLabel 5 = 10 and card = 5, but
no production theorem currently performs that sum. No arbitrary inequality,
toy, axiom, or sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace SignedMagnitudeConditionalAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceEtaleThetaTheory
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.PaperSignedHullSignedActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeComparisonProof
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open scoped BigOperators

universe ua uv upi umon ui uL uC uG uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (D : SourcePilotRegionDonors (l := l) (V := V) I)

/-- The finite theta label cardinality. -/
abbrev thetaCard : Nat := Fintype.card (SignedLabel l.value)

/-- The exact Gaussian-exponent average used by the signed source-theater
procession. -/
def SignedThetaAverageCandidate (l : PrimeGeFive) : Real :=
  Real.log 5 *
    ((Finset.univ.sum
      (fun j : SignedLabel l.value => ((gaussExponent j.1).toNat : Real))) /
      (Fintype.card (SignedLabel l.value) : Real))

/-- The source-theater C3 theta packet is the concrete source theater packet. -/
theorem actualSignedC3_thetaPacket_eq_sourceTheater
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    (actualSignedC3 (l := l) (V := V) (I := I) D).thetaPacket =
      (sourceTheater l).thetaPacket :=
  rfl

/-- The actual signed average cast in terms of the finite Gaussian sum. -/
theorem actualSignedC3_signedAverage_eq_candidate
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    (c3ThetaSignedProcession
      (actualSignedC3 (l := l) (V := V) (I := I) D)).average =
      SignedThetaAverageCandidate (l := l) := by
  rw [c3ThetaSignedProcession_average_eq_neg, c3ThetaProcession_average]
  rw [actualSignedC3_thetaPacket_eq_sourceTheater]
  rw [(sourceTheater l).thetaPacket.logVolume_eq_sum]
  have hlog : forall j : SignedLabel l.value,
      Real.log ((sourceTheater l).thetaPacket.scale j) =
        ((gaussExponent j.1).toNat : Real) * (-Real.log 5) := by
    intro j
    exact sourceTheater_theta_log_scale (l := l) j
  simp_rw [hlog]
  rw [← Finset.sum_mul]
  unfold SignedThetaAverageCandidate
  ring

/-- The exact real bound sufficient for the signed magnitude comparison. -/
def SignedMagnitudeBound
    (D : SourcePilotRegionDonors (l := l) (V := V) I) : Prop :=
  SignedThetaAverageCandidate (l := l) <=
    paperQPilotLogMagnitude
      (actualSignedC3 (l := l) (V := V) (I := I) D)

/-- The signed magnitude comparison follows from the exact real bound. -/
theorem signedThetaAverageLeQMagnitude_of_magnitudeBound
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (h : SignedMagnitudeBound (l := l) (V := V) (I := I) D) :
    SignedThetaAverageLeQMagnitude (l := l) (V := V) (I := I) D := by
  unfold SignedThetaAverageLeQMagnitude SignedMagnitudeBound at *
  rw [actualSignedC3_signedAverage_eq_candidate]
  exact h

/-- Exact arithmetic comparison for l = 5: the finite Gaussian average is
2 log 5. This is the only finite-sum computation not performed here. -/
def FiveGaussExponentAverageIdentity : Prop :=
  SignedThetaAverageCandidate (l := fivePrimeLabel) = 2 * Real.log 5

/-- The actual q-pilot magnitude is at least 2 log 5 when the q norm is at most
1/25. -/
theorem paperQPilotLogMagnitude_ge_two_log_five_of_qNorm_le
    (h : ‖(actualSignedC3 (l := l) (V := V) (I := I) D).q.q‖ <= (1 / 25 : Real)) :
    2 * Real.log 5 <=
      paperQPilotLogMagnitude
        (actualSignedC3 (l := l) (V := V) (I := I) D) := by
  have hqpos : 0 < ‖(actualSignedC3 (l := l) (V := V) (I := I) D).q.q‖ :=
    ArithmeticQPilotLogVolume.qNorm_pos
      (actualSignedC3 (l := l) (V := V) (I := I) D).q
  have hlog : Real.log ‖(actualSignedC3 (l := l) (V := V) (I := I) D).q.q‖ <=
      Real.log (1 / 25 : Real) :=
    Real.log_le_log hqpos h
  have h25 : Real.log (1 / 25 : Real) = -2 * Real.log 5 := by
    have hfactor : (1 / 25 : Real) = (5 : Real)⁻¹ * (5 : Real)⁻¹ := by
      norm_num
    rw [hfactor, Real.log_mul (by norm_num) (by norm_num), Real.log_inv]
    ring
  unfold paperQPilotLogMagnitude
  rw [paperQPilotLogVolume_eq_log_norm]
  linarith

/-- For l = 5, qNorm <= 1/25 plus the exact finite Gaussian average identity
gives the signed magnitude comparison. -/
theorem signedThetaAverageLeQMagnitude_five_of_qNorm_le
    (h : ‖(actualSignedC3 (l := fivePrimeLabel) (V := V) (I := I) D).q.q‖ <=
      (1 / 25 : Real))
    (hfive : FiveGaussExponentAverageIdentity) :
    SignedThetaAverageLeQMagnitude (l := fivePrimeLabel) (V := V) (I := I) D := by
  apply signedThetaAverageLeQMagnitude_of_magnitudeBound
  unfold SignedMagnitudeBound
  rw [hfive]
  exact paperQPilotLogMagnitude_ge_two_log_five_of_qNorm_le
    (l := fivePrimeLabel) (V := V) (I := I) D h

/-- Exact arithmetic form: the target for l = 5 reduces to the finite average
identity plus the q-norm bound. No bound is assumed beyond these. -/
theorem signedThetaAverageLeQMagnitude_five_iff_arithmetic
    (h : ‖(actualSignedC3 (l := fivePrimeLabel) (V := V) (I := I) D).q.q‖ <=
      (1 / 25 : Real)) :
    (FiveGaussExponentAverageIdentity ->
      SignedThetaAverageLeQMagnitude (l := fivePrimeLabel) (V := V) (I := I) D) :=
  signedThetaAverageLeQMagnitude_five_of_qNorm_le
    (l := fivePrimeLabel) (V := V) (I := I) D h

end SignedMagnitudeConditionalAdapted
end XiFPaper
end LeanFormal.IUT
end
