import tmp.sheaf.xif.paper.C3GaussianThetaPacketActual
import tmp.sheaf.xif.paper.SignedAverageBoundActual
import tmp.sheaf.xif.paper.SignedAverageBoundQOneFifthAdapted

/-! # Concrete q=1/5 magnitude versus signed average: actual reduction and obstacle

For the concrete source Gaussian C3 (theta packet q = 1/5), the actual signed
average is

  c3ThetaSignedProcession.average
    = log 5 * (gaussExponentSum / card(SignedLabel l.value)).

This file computes that formula for the concrete Gaussian C3 and reduces the
proposed q-magnitude bound

  signedAverage <= paperQPilotLogMagnitude C3

to the exact arithmetic comparison between paperQPilotLogMagnitude and log 5,
and the Gauss-exponent sum/coefficient.  It proves the negation of the bound
from the exact positive obstacle (q-magnitude = log 5 and sum > card); the
obstacle itself is recorded, not faked.

No inequality is asserted.  No sorry, axiom, True, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ConcreteQMagnitudeSourceComparisonActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperSignedHullSignedActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
open LeanFormal.IUT.XiFPaper.SignedAverageBoundActual
open LeanFormal.IUT.XiFPaper.SignedAverageBoundQOneFifthAdapted
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open scoped BigOperators

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

variable (D : SourcePilotRegionDonors (l := l) (V := V) I)

/-- The concrete source Gaussian C3 (theta packet q = 1/5). -/
abbrev concreteGaussianC3 : SourcePilotRegionData (l := l) (V := V) I :=
  actualGaussianC3 (l := l) (V := V) (I := I) D

/-- The concrete signed average. -/
noncomputable def concreteSignedAverage : Real :=
  (c3ThetaSignedProcession (concreteGaussianC3 (l := l) (V := V) (I := I) D)).average

/-- The actual signed-average formula at q = 1/5. -/
theorem concreteSignedAverage_eq_log5_mul_sum_div_card :
    concreteSignedAverage (l := l) (V := V) (I := I) D =
      Real.log (5 : Real) *
        ((gaussExponentSum (l := l) : Real) /
          (Fintype.card (SignedLabel l.value) : Real)) := by
  unfold concreteSignedAverage concreteGaussianC3
  exact actualSignedC3_signedAverage_eq_log5_mul_sum_div_card
    (l := l) (V := V) (I := I) D

/-- The proposed q-magnitude bound for the concrete Gaussian C3. -/
def ConcreteQMagnitudeBound : Prop :=
  concreteSignedAverage (l := l) (V := V) (I := I) D <=
    paperQPilotLogMagnitude (concreteGaussianC3 (l := l) (V := V) (I := I) D)

/-- The exact arithmetic obstacle: the actual q-pilot magnitude is log 5 and
the Gauss-exponent sum exceeds the label cardinality. -/
def ConcreteQMagnitudeObstacle : Prop :=
  paperQPilotLogMagnitude (concreteGaussianC3 (l := l) (V := V) (I := I) D) =
      Real.log (5 : Real) ∧
    Fintype.card (SignedLabel l.value) < gaussExponentSum (l := l)

/-- At q = 1/5, the proposed bound is equivalent to the coefficient being at
most one (assuming the actual q magnitude is log 5). -/
theorem concreteQMagnitudeBound_iff_coefficientLeOne
    (hqmag : paperQPilotLogMagnitude
      (concreteGaussianC3 (l := l) (V := V) (I := I) D) = Real.log (5 : Real)) :
    ConcreteQMagnitudeBound (l := l) (V := V) (I := I) D ↔
      (gaussExponentSum (l := l) : Real) /
          (Fintype.card (SignedLabel l.value) : Real) <= 1 := by
  unfold ConcreteQMagnitudeBound
  rw [concreteSignedAverage_eq_log5_mul_sum_div_card (l := l) (V := V) (I := I) D,
    hqmag]
  have hlog : (0 : Real) < Real.log (5 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 5)
  constructor
  · intro h
    have h' : Real.log (5 : Real) *
        ((gaussExponentSum (l := l) : Real) /
          (Fintype.card (SignedLabel l.value) : Real)) <=
        Real.log (5 : Real) * 1 := by simpa using h
    exact (mul_le_mul_right hlog).mp h'
  · intro h
    calc
      Real.log (5 : Real) *
          ((gaussExponentSum (l := l) : Real) /
            (Fintype.card (SignedLabel l.value) : Real)) <=
          Real.log (5 : Real) * 1 := by gcongr
      _ = Real.log (5 : Real) := by ring

/-- The exact arithmetic obstacle disproves the proposed q-magnitude bound. -/
theorem not_concreteQMagnitudeBound_of_obstacle
    (h : ConcreteQMagnitudeObstacle (l := l) (V := V) (I := I) D) :
    ¬ ConcreteQMagnitudeBound (l := l) (V := V) (I := I) D := by
  rcases h with ⟨hqmag, hsum⟩
  have hcardNat : 0 < Fintype.card (SignedLabel l.value) := by
    rw [SignedLabel.card_signedLabel]
    exact l.prime.pos
  have hcard : (0 : Real) < (Fintype.card (SignedLabel l.value) : Real) := by
    exact_mod_cast hcardNat
  have hsumR : (Fintype.card (SignedLabel l.value) : Real) <
      (gaussExponentSum (l := l) : Real) := by exact_mod_cast hsum
  have hcoeff : 1 < (gaussExponentSum (l := l) : Real) /
      (Fintype.card (SignedLabel l.value) : Real) := by
    rw [lt_div_iff₀ hcard]
    simpa using hsumR
  have hlog : (0 : Real) < Real.log (5 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 5)
  unfold ConcreteQMagnitudeBound
  rw [concreteSignedAverage_eq_log5_mul_sum_div_card (l := l) (V := V) (I := I) D,
    hqmag]
  exact not_le_of_gt (mul_lt_mul_of_pos_left hcoeff hlog)

end LeanFormal.IUT.XiFPaper.ConcreteQMagnitudeSourceComparisonActualAdapted

end
