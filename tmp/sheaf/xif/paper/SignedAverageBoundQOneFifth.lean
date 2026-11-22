import tmp.sheaf.xif.paper.SignedAverageBoundActual

/-!
# Signed average under q = 1/5 and the exact sum inequality

For the actual source-theater theta packet q = gaussianFiveThetaQ = 1/5,

  log(scale j) = (gaussExponent j).toNat * log(1/5)
               = -(gaussExponent j).toNat * log 5,

so the signed procession has

  c3ThetaSignedProcession.average
    = log 5 * (gaussExponentSum / card(SignedLabel l.value)).

The proposed bound average <= log 5 is therefore exactly

  gaussExponentSum <= card(SignedLabel l.value).

This file proves that equivalence from the actual formula.  It does not assert
the sum inequality.  Arithmetically the inequality is false already at l = 5:
the signed labels are -2,-1,0,1,2, the exponent sum is 10, and the cardinality
is 5.  Thus a bound average <= log 5 cannot be obtained from the actual q = 1/5
data without an additional (false) sum inequality.

No arbitrary inequality is asserted.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.SignedAverageBoundQOneFifth

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperSignedHullSignedActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.SignedAverageBoundActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open scoped BigOperators

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual source-theater signed average in the q = 1/5 case. -/
theorem actualSignedC3_signedAverage_eq
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    (c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := V) (I := I) D)).average =
      Real.log (5 : Real) *
        ((gaussExponentSum (l := l) : Real) /
          (Fintype.card (SignedLabel l.value) : Real)) :=
  actualSignedC3_signedAverage_eq_log5_mul_sum_div_card (l := l) (V := V) (I := I) D

/-- The exact sum inequality: the Gauss-exponent sum is at most the number of
signed labels. -/
def GaussSumLeCard : Prop :=
  gaussExponentSum (l := l) <= Fintype.card (SignedLabel l.value)

/-- The proposed average bound average <= log 5. -/
def SignedAverageLeLogFive
    (D : SourcePilotRegionDonors (l := l) (V := V) I) : Prop :=
  (c3ThetaSignedProcession
      (actualSignedC3 (l := l) (V := V) (I := I) D)).average <=
    Real.log (5 : Real)

/-- The average bound is equivalent to the exact sum inequality. -/
theorem actualSignedC3_signedAverageLeLogFive_iff
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    SignedAverageLeLogFive (l := l) (V := V) (I := I) D ↔
      GaussSumLeCard (l := l) := by
  unfold SignedAverageLeLogFive GaussSumLeCard
  rw [actualSignedC3_signedAverage_eq (l := l) (V := V) (I := I) D]
  have hlog : (0 : Real) < Real.log (5 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 5)
  have hcardNat : 0 < Fintype.card (SignedLabel l.value) := by
    rw [SignedLabel.card_signedLabel]
    exact l.prime.pos
  have hcard : (0 : Real) < (Fintype.card (SignedLabel l.value) : Real) := by
    exact_mod_cast hcardNat
  constructor
  · intro h
    have h' : Real.log (5 : Real) *
        ((gaussExponentSum (l := l) : Real) /
          (Fintype.card (SignedLabel l.value) : Real)) <=
        Real.log (5 : Real) * 1 := by
      simpa using h
    have hquot : (gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real) <= 1 :=
      (mul_le_mul_right hlog).mp h'
    have hsum : (gaussExponentSum (l := l) : Real) <=
        (Fintype.card (SignedLabel l.value) : Real) :=
      (div_le_iff₀ hcard).mp hquot
    exact_mod_cast hsum
  · intro h
    have hsum : (gaussExponentSum (l := l) : Real) <=
        (Fintype.card (SignedLabel l.value) : Real) := by
      exact_mod_cast h
    have hquot : (gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real) <= 1 :=
      (div_le_iff₀ hcard).mpr (by simpa using hsum)
    calc
      Real.log (5 : Real) *
          ((gaussExponentSum (l := l) : Real) /
            (Fintype.card (SignedLabel l.value) : Real)) <=
          Real.log (5 : Real) * 1 := by gcongr
      _ = Real.log (5 : Real) := by ring

/-- Conditional signed-average/q-magnitude bound from the exact sum inequality
and the q-magnitude identification. -/
theorem signedThetaAverageLeQMagnitude_of_sumLeCard
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (hqmag : paperQPilotLogMagnitude
      (actualSignedC3 (l := l) (V := V) (I := I) D) = Real.log (5 : Real))
    (hsum : GaussSumLeCard (l := l)) :
    SignedThetaAverageLeQMagnitude (l := l) (V := V) (I := I) D := by
  unfold SignedThetaAverageLeQMagnitude
  rw [hqmag]
  exact (actualSignedC3_signedAverageLeLogFive_iff
    (l := l) (V := V) (I := I) D).mpr hsum

/-- Exact missing arithmetic input: the Gauss-exponent sum inequality.  This is
the sole condition left by the average bound at q = 1/5. -/
def ExactSumInequalityInput : Prop :=
  GaussSumLeCard (l := l)

/-- The conditional bound under the exact sum inequality. -/
theorem signedThetaAverageLeQMagnitude_of_exactSum
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (hqmag : paperQPilotLogMagnitude
      (actualSignedC3 (l := l) (V := V) (I := I) D) = Real.log (5 : Real))
    (hsum : ExactSumInequalityInput (l := l)) :
    SignedThetaAverageLeQMagnitude (l := l) (V := V) (I := I) D :=
  signedThetaAverageLeQMagnitude_of_sumLeCard
    (l := l) (V := V) (I := I) D hqmag hsum

end LeanFormal.IUT.XiFPaper.SignedAverageBoundQOneFifth

end
