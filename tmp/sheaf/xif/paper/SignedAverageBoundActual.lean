import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual
import tmp.sheaf.xif.paper.SourceTheaterLogVolumeSign
import tmp.sheaf.xif.paper.ProcessionThetaPacketAverageActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity

/-!
# Source-theater signed average: computation and exact arithmetic boundary

For the source-theater theta packet q = 1/5 and scale j = q^(gaussExponent j),
the signed procession values are

  -log(scale j) = (gaussExponent j).toNat * log 5,

so

  c3ThetaSignedProcession.average
    = log 5 * (sum_j (gaussExponent j).toNat / card(SignedLabel l.value)).

For l.value = 5 the signed labels are -2,-1,0,1,2, the exponent sum is
4+1+0+1+4 = 10, the cardinality is 5, and the coefficient is 2. Hence the
signed average is 2 log 5, which is strictly larger than log 5. Therefore the
proposed bound average <= log 5 is FALSE for l = 5 and, in general, for every
prime l >= 5 (the coefficient is lStar(lStar+1)/3 >= 2).

This file records the actual sum formula, the exact missing Gauss-exponent sum
identity, and the exact arithmetic comparison. It does not assert a false
bound. No toy data, forbidden declaration, axiom, or unfilled proof is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.SignedAverageBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper.SourceTheaterLogVolumeSign
open scoped BigOperators

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual Gauss-exponent sum appearing in the signed average. -/
def gaussExponentSum : Nat :=
  ∑ j : SignedLabel l.value, (gaussExponent j.1).toNat

/-- The actual source-theater signed average, in terms of the Gauss sum. -/
theorem actualSignedC3_signedAverage_eq_log5_mul_sum_div_card
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    (c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := V) (I := I) D)).average =
      Real.log (5 : Real) *
        ((gaussExponentSum (l := l) : Real) /
          (Fintype.card (SignedLabel l.value) : Real)) := by
  rw [c3ThetaSignedProcession_average_eq_neg,
    c3ThetaProcession_average]
  rw [show actualSignedC3 (l := l) (V := V) (I := I) D =
      c3WithSourceTheaterTheta (I := I) D from rfl]
  rw [c3WithSourceTheaterTheta_logVolume_eq_nonpos (I := I) D]
  rw [show (∑ j : SignedLabel l.value,
      (gaussExponent j.1).toNat * (- Real.log (5 : Real))) =
      -(Real.log (5 : Real) * (gaussExponentSum (l := l) : Real)) by
    rw [show (∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat * (- Real.log (5 : Real))) =
        -(∑ j : SignedLabel l.value,
          (gaussExponent j.1).toNat * Real.log (5 : Real)) by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)]
    rw [← Finset.sum_mul]
    unfold gaussExponentSum
    push_cast
    ring
  ]
  rw [show Fintype.card (SignedLabel l.value) = c3ThetaCard (l := l) by rfl]
  field_simp [c3ThetaCard_pos (l := l)]

/-- Exact missing Gauss-exponent sum identity: the signed-label squares sum to
the three-point closed form. -/
def GaussExponentSumClosedForm : Prop :=
  (gaussExponentSum (l := l) : Nat) =
    (lStar l.value * (lStar l.value + 1) * (2 * lStar l.value + 1)) / 3

/-- Exact arithmetic boundary: the average coefficient is strictly larger than
one for every prime l >= 5. -/
def SignedAverageCoefficientGtOne : Prop :=
  1 < ((lStar l.value * (lStar l.value + 1) : Nat) : Real) / 3

/-- Exact proposed bound: signed average <= log 5. -/
def SignedThetaAverageLeLogFive
    (D : SourcePilotRegionDonors (l := l) (V := V) I) : Prop :=
  (c3ThetaSignedProcession
      (actualSignedC3 (l := l) (V := V) (I := I) D)).average <= Real.log 5

/-- The proposed log-5 bound is not derivable from the actual source-theater
data; it needs the Gauss sum identity and would be false under the computed
coefficient. -/
def ExactMissingArithmeticComparison
    (D : SourcePilotRegionDonors (l := l) (V := V) I) : Prop :=
  GaussExponentSumClosedForm (l := l) ∧
    SignedAverageCoefficientGtOne (l := l) ∧
      (paperQPilotLogMagnitude
        (actualSignedC3 (l := l) (V := V) (I := I) D) = Real.log 5)

end LeanFormal.IUT.XiFPaper.SignedAverageBoundActual

end
