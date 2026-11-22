import tmp.sheaf.xif.paper.ThetaPacketQIdentificationActual
import tmp.sheaf.xif.paper.PaperSignedHullSignedActual
import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteIntegralHodgeTheaterExample
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier

/-!
# Source-theater theta packet log-volume is nonpositive

The source theater of the concrete Gaussian C-stage has theta packet

  FiniteThetaPacket.ofQ gaussianFiveThetaQ gaussianFiveThetaQ_pos,

with q = gaussianFiveThetaQ = 1/5 and scale j = q ^ (gaussExponent j). Hence

  log(scale j) = (gaussExponent j).toNat * log q
               = (gaussExponent j).toNat * (-log 5),

and each term is nonpositive because the exponent is nonnegative and log 5 > 0.
This proves ThetaPacketLogVolumeNonpos for c3WithSourceTheaterTheta, using the
actual q value and the actual log-volume sum formula.  No inequality is assumed.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.SourceTheaterLogVolumeSign

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier

local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

variable {l : PrimeGeFive}

/-- The actual source-theater packet log-volume, written in terms of the
gaussian exponents and the actual q-log -log 5. -/
theorem sourceTheater_packet_logVolume_formula
    (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat * (- Real.log (5 : Real)) := by
  rw [FiniteThetaPacket.logVolume_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [FiniteThetaPacket.log_scale, sourceTheater_theta_q_log]

/-- The same log-volume through the actual gaussian integral-theater formula. -/
theorem sourceTheater_packet_logVolume_eq_gaussian
    (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat *
          Multiplicative.toAdd
            (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  change (concreteInitialThetaCStageTheater l).thetaPacket.logVolume =
    ∑ j : SignedLabel l.value,
      (gaussExponent j.1).toNat *
        Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5))
  exact concreteInitialThetaCStageTheater_logVolume l

/-- Each summand is nonpositive: nonnegative exponent times -log 5. -/
theorem sourceTheater_packet_logVolume_summand_nonpos
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (gaussExponent j.1).toNat * (- Real.log (5 : Real)) <= 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos
    (Nat.cast_nonneg (gaussExponent j.1).toNat)
    (neg_nonpos.mpr (le_of_lt (Real.log_pos (by norm_num : (1 : Real) < 5))))

/-- Actual source-theater packet log-volume is nonpositive. -/
theorem sourceTheater_packet_logVolume_nonpos
    (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.logVolume <= 0 := by
  rw [sourceTheater_packet_logVolume_formula]
  exact Finset.sum_nonpos (fun j _ =>
    sourceTheater_packet_logVolume_summand_nonpos l j)

/-- The sign package for the actual source-theater C3. -/
theorem c3WithSourceTheaterTheta_logVolume_nonpos
    {V : Type*} {I : OriginalInput l V}
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    ThetaPacketLogVolumeNonpos
      (c3WithSourceTheaterTheta (I := I) D) := by
  unfold ThetaPacketLogVolumeNonpos
  rw [c3WithSourceTheaterTheta_thetaPacket]
  exact sourceTheater_packet_logVolume_nonpos l

/-- The signed source-theater packet log-volume itself. -/
theorem c3WithSourceTheaterTheta_logVolume_eq_nonpos
    {V : Type*} {I : OriginalInput l V}
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    (c3WithSourceTheaterTheta (I := I) D).thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat * (- Real.log (5 : Real)) := by
  rw [c3WithSourceTheaterTheta_thetaPacket]
  exact sourceTheater_packet_logVolume_formula l

/-- The exact positive-exponent statement: any nonzero signed label contributes
a strictly negative summand. -/
theorem sourceTheater_packet_logVolume_summand_neg_of_ne_zero
    (l : PrimeGeFive) (j : SignedLabel l.value) (hj : j.1 ≠ 0) :
    (gaussExponent j.1).toNat * (- Real.log (5 : Real)) < 0 := by
  have hlog : (0 : Real) < Real.log (5 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 5)
  have hexp : 0 < (gaussExponent j.1).toNat := by
    unfold gaussExponent
    have hnonzero : (j.1 : Int) ≠ 0 := hj
    have hpos : 0 < (j.1 : Int) ^ 2 := by
      exact sq_pos_of_ne_zero hnonzero
    have hnonneg : 0 <= gaussExponent j.1 := le_of_lt hpos
    have hto : ((gaussExponent j.1).toNat : Int) = gaussExponent j.1 :=
      Int.toNat_of_nonneg hnonneg
    omega
  exact mul_neg_of_pos_of_neg (Nat.cast_pos.mpr hexp) (neg_lt_zero.mpr hlog)

end LeanFormal.IUT.XiFPaper.SourceTheaterLogVolumeSign

end