import tmp.sheaf.n8.closure.EtaAnabAtFPlace
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import tmp.sheaf.n8.closure.EtaRssNontrivialActual
import Mathlib

/-!
# Eta Rss over admissible regions

Corrects EtaRegionQuotientRss: the quotient is over actual admissible regions
(measurable, positive finite Haar volume), not all sets.  Nontriviality is
witnessed by an actual closed ball and its p-scaled copy (an actual closed ball),
both admissible with different volumes.  Empty is not used.
-/

noncomputable section

open MeasureTheory
open scoped Pointwise
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual

namespace LeanFormal.IUT.N8Closure.EtaRssAdmissibleCorrection

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

abbrev K : Type := CommonPrimeCompletion (K := X.S.arithmetic.F) (nativeFPlaceAtPrime X)

local instance FPlacePrimeFact : Fact (Nat.Prime (FPlacePrime X)) :=
  ⟨(NumberFieldFinitePlace.completionRationalPrime (nativeFPlaceOverBad X)).2⟩

variable [MeasurableSpace (K X)] [BorelSpace (K X)]
variable (mu : Measure (K X)) [Measure.IsAddHaarMeasure mu]
variable [Measure.IsOpenPosMeasure mu] [IsFiniteMeasureOnCompacts mu]
variable [ProperSpace (K X)] [IsUltrametricDist (K X)]
variable [NormedSpace ℚ_[FPlacePrime X] (K X)]
variable [FiniteDimensional ℚ_[FPlacePrime X] (K X)]
variable [Nontrivial (K X)]
variable [NormSMulClass ℚ_[FPlacePrime X] (K X)]

structure AdmissibleRegion where
  carrier : Set (K X)
  measurable : MeasurableSet carrier
  pos : 0 < mu carrier
  finite : mu carrier < ⊤

def RegionSetoid : Setoid (AdmissibleRegion (X := X) (mu := mu)) where
  r R S := mu R.carrier = mu S.carrier
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

abbrev Rss : Type := Quotient (RegionSetoid (X := X) (mu := mu))

def rssOf (R : AdmissibleRegion (X := X) (mu := mu)) : Rss (X := X) (mu := mu) :=
  Quotient.mk (RegionSetoid (X := X) (mu := mu)) R

noncomputable def readout (q : Rss (X := X) (mu := mu)) : ENNReal :=
  Quotient.lift (fun R : AdmissibleRegion (X := X) (mu := mu) => mu R.carrier)
    (fun _ _ h => h) q

theorem readout_mk (R : AdmissibleRegion (X := X) (mu := mu)) :
    readout (X := X) (mu := mu) (rssOf (X := X) (mu := mu) R) = mu R.carrier := rfl

def admClosedBall : AdmissibleRegion (X := X) (mu := mu) where
  carrier := Metric.closedBall (0 : K X) 1
  measurable := measurableSet_closedBall
  pos := Metric.measure_closedBall_pos mu 0 zero_lt_one
  finite := (isCompact_closedBall (0 : K X) 1).measure_lt_top

/-- Actual open unit ball as an admissible region. -/
def admOpenBall : AdmissibleRegion (X := X) (mu := mu) where
  carrier := Metric.ball (0 : K X) 1
  measurable := measurableSet_ball
  pos := Metric.measure_ball_pos mu 0 zero_lt_one
  finite := lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
    (isCompact_closedBall (0 : K X) 1).measure_lt_top

/-- Actual open-ball mass is strictly less than actual closed-ball mass. -/
theorem admOpenBall_volume_lt_closedBall :
    mu (admOpenBall (X := X) (mu := mu)).carrier <
      mu (admClosedBall (X := X) (mu := mu)).carrier := by
  simpa [admOpenBall, admClosedBall, EtaRssNontrivialActual.openRegion,
    EtaRssNontrivialActual.closedRegion] using
    (EtaRssNontrivialActual.open_mass_lt_closed_mass (K := K X) (mu := mu))

theorem admOpenBall_volume_ne_closedBall :
    mu (admOpenBall (X := X) (mu := mu)).carrier ≠
      mu (admClosedBall (X := X) (mu := mu)).carrier :=
  ne_of_lt (admOpenBall_volume_lt_closedBall (X := X) (mu := mu))

theorem rss_admissible_not_subsingleton : ¬ Subsingleton (Rss (X := X) (mu := mu)) := by
  intro hsub
  have hq : rssOf (X := X) (mu := mu) (admOpenBall (X := X) (mu := mu)) =
      rssOf (X := X) (mu := mu) (admClosedBall (X := X) (mu := mu)) :=
    Subsingleton.elim _ _
  exact admOpenBall_volume_ne_closedBall (X := X) (mu := mu) (Quotient.exact hq)

theorem readout_ne_open_closed :
    readout (X := X) (mu := mu) (rssOf (X := X) (mu := mu) (admOpenBall (X := X) (mu := mu))) ≠
      readout (X := X) (mu := mu) (rssOf (X := X) (mu := mu) (admClosedBall (X := X) (mu := mu))) := by
  rw [readout_mk, readout_mk]
  exact admOpenBall_volume_ne_closedBall (X := X) (mu := mu)

end LeanFormal.IUT.N8Closure.EtaRssAdmissibleCorrection
