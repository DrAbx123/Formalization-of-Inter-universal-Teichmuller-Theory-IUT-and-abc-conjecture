import tmp.sheaf.n8.closure.EtaRssAdmissibleCorrection
import Mathlib

/-!
# Global Rss at the actual F completion

The global region carrier is the actual F completion at nativeFPlaceOverBad
(the same carrier as the local admissible Rss), NOT the base Fmod
localFieldAt.  Therefore the local admissible classes/readout connect to the
global F-level classes directly, with no carrier bridge.  The bridge is the
identity class map on the common carrier; no arbitrary map is introduced.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaRssAdmissibleCorrection

namespace LeanFormal.IUT.N8Closure.EtaGlobalRssAtF

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (K X)] [BorelSpace (K X)]
variable (muK : Measure (K X)) [Measure.IsAddHaarMeasure muK]
variable [Measure.IsOpenPosMeasure muK] [IsFiniteMeasureOnCompacts muK]
variable [ProperSpace (K X)] [IsUltrametricDist (K X)]
variable [NormedSpace ℚ_[FPlacePrime X] (K X)]
variable [FiniteDimensional ℚ_[FPlacePrime X] (K X)]
variable [Nontrivial (K X)]
variable [NormSMulClass ℚ_[FPlacePrime X] (K X)]

/-- F-level global region carrier: actual F completion, not base Fmod. -/
abbrev GlobalRegionAtF : Type := Set (K X)

/-- F-level global admissible regions are the local admissible regions. -/
abbrev GlobalAdmissibleAtF : Type := AdmissibleRegion (X := X) (mu := muK)

/-- F-level global equal-volume Rss. -/
abbrev GlobalRssAtF : Type := Rss (X := X) (mu := muK)

/-- Actual F-level global open region. -/
def globalOpenRegionAtF : GlobalRegionAtF X :=
  (admOpenBall (X := X) (mu := muK)).carrier

/-- Actual F-level global closed region. -/
def globalClosedRegionAtF : GlobalRegionAtF X :=
  (admClosedBall (X := X) (mu := muK)).carrier

/-- Actual F-level global open class. -/
def globalOpenClassAtF : GlobalRssAtF X muK :=
  rssOf (X := X) (mu := muK) (admOpenBall (X := X) (mu := muK))

/-- Actual F-level global closed class. -/
def globalClosedClassAtF : GlobalRssAtF X muK :=
  rssOf (X := X) (mu := muK) (admClosedBall (X := X) (mu := muK))

/-- Direct class map: local admissible class -> global F-level class, identity
on the shared carrier. -/
def localClassToGlobalAtF (q : Rss (X := X) (mu := muK)) :
    GlobalRssAtF X muK := q

/-- Global F-level readout. -/
noncomputable def globalReadoutAtF (q : GlobalRssAtF X muK) : ENNReal :=
  readout (X := X) (mu := muK) q

theorem globalReadoutAtF_eq_local (q : Rss (X := X) (mu := muK)) :
    globalReadoutAtF X muK
      (localClassToGlobalAtF X muK q) =
      readout (X := X) (mu := muK) q := rfl

theorem localClassToGlobalAtF_open :
    localClassToGlobalAtF X muK
      (rssOf (X := X) (mu := muK) (admOpenBall (X := X) (mu := muK))) =
      rssOf (X := X) (mu := muK) (admOpenBall (X := X) (mu := muK)) := rfl

theorem globalOpenClass_ne_globalClosedClass :
    rssOf (X := X) (mu := muK) (admOpenBall (X := X) (mu := muK)) ≠
      rssOf (X := X) (mu := muK) (admClosedBall (X := X) (mu := muK)) := by
  intro h
  exact admOpenBall_volume_ne_closedBall (X := X) (mu := muK) (Quotient.exact h)

/-- Common-carrier bridge: the local admissible classes/readout are exactly the
global F-level classes/readout; no base Fmod carrier and no carrier transport. -/
theorem local_global_common_carrier_bridge :
    (localClassToGlobalAtF X muK
        (rssOf (X := X) (mu := muK) (admOpenBall (X := X) (mu := muK)))) =
        globalOpenClassAtF X muK ∧
      localClassToGlobalAtF X muK
          (rssOf (X := X) (mu := muK) (admOpenBall (X := X) (mu := muK))) ≠
        localClassToGlobalAtF X muK
          (rssOf (X := X) (mu := muK) (admClosedBall (X := X) (mu := muK))) ∧
      globalReadoutAtF X muK
          (localClassToGlobalAtF X muK
            (rssOf (X := X) (mu := muK) (admOpenBall (X := X) (mu := muK)))) =
        readout (X := X) (mu := muK)
          (rssOf (X := X) (mu := muK) (admOpenBall (X := X) (mu := muK))) := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · exact globalOpenClass_ne_globalClosedClass X muK
  · rfl

end LeanFormal.IUT.N8Closure.EtaGlobalRssAtF
