import tmp.sheaf.xif.paper.SourceSignedLogVolumeCorrectedActual
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.CorrectedHullCounterexampleActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.SourceSignedLogVolumeCorrectedActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (n : ThetaPilotCarrier l) (v : V)

/-- The theta packet q at the hull stage. -/
noncomputable def hullQ : Real :=
  (I.theaterAt (n.val : Int) 0).thetaPacket.q

theorem hullQ_pos : 0 < hullQ (I := I) n := 
  (I.theaterAt (n.val : Int) 0).thetaPacket.q_pos

theorem hullQ_eq_oneColumnQAtZero :
    hullQ (I := I) n = I.oneColumnQAtZero := by
  unfold hullQ oneColumnQAtZero oneColumnQ oneColumnPacket
  exact I.linkAt_q (n.val : Int) 0 1 0

theorem correctedSourceHullLogVolume_eq :
    correctedSourceHullLogVolume (I := I) (n := n) v =
      -((∑ j : SignedLabel l.value,
          ((gaussExponent j.1).toNat : Real)) * Real.log (hullQ (I := I) n)) := by
  unfold correctedSourceHullLogVolume hullQ
  change (∑ j : SignedLabel l.value,
      -Real.log ((I.theaterAt (n.val : Int) 0).thetaPacket.scale j)) =
    -((∑ j : SignedLabel l.value,
        ((gaussExponent j.1).toNat : Real)) *
      Real.log ((I.theaterAt (n.val : Int) 0).thetaPacket.q))
  rw [Finset.sum_neg_distrib]
  rw [neg_inj]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [(I.theaterAt (n.val : Int) 0).thetaPacket.log_scale j]

theorem correctedSourceXifComparison_false_of_q_lt_one
    (hq : I.oneColumnQAtZero < 1)
    (hsum : 1 < (∑ j : SignedLabel l.value,
      ((gaussExponent j.1).toNat : Real))) :
    ¬ CorrectedSourceXifComparison (I := I) (v := v) (n := n) := by
  intro h
  have hqpos : 0 < I.oneColumnQAtZero := I.oneColumnQAtZero_pos
  have hlog : Real.log I.oneColumnQAtZero < 0 :=
    Real.log_neg hqpos hq
  have hqeq : hullQ (I := I) n = I.oneColumnQAtZero :=
    hullQ_eq_oneColumnQAtZero (I := I) n
  have hqsign : I.qPilotSignedLogVolume = Real.log I.oneColumnQAtZero := by
    unfold qPilotSignedLogVolume
    rw [abs_of_neg hlog]
    ring
  have hhull := correctedSourceHullLogVolume_eq (I := I) n v
  unfold CorrectedSourceXifComparison correctedSourceSignedImageLogVolume
    correctedSourceSignedHullLogVolume at h
  rw [hqsign, hhull] at h
  rw [hqeq] at h
  set L := Real.log I.oneColumnQAtZero
  set S := (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real))
  have hS : 1 < S := hsum
  have hL : L < 0 := hlog
  have hnonneg : 0 <= (S - 1) * L := by
    nlinarith [h]
  have hneg : (S - 1) * L < 0 := by
    exact mul_neg_of_pos_of_neg (by linarith) hL
  linarith

end LeanFormal.IUT.XiFPaper.CorrectedHullCounterexampleActual

end
