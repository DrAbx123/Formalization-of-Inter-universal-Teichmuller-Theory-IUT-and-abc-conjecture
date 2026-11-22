import tmp.sheaf.n8.closure.EtaQOClassGlobalActual
import Mathlib

/-!
# QO readout relation via Haar normalization

Mathlib Haar uniqueness gives equality of two Haar measures on an everywhere
positive set once their common scalar factor is normalized at an open set.  We
prove this conditional Haar lemma and record the exact application target for
the canonical GlobalRssAtF measure and the multiradial QCompletion Haar measure.
The missing actual inputs are the normalizations mu_K(O)=1 and mu_Q(O)=1 (and
the common-carrier measure transport); no arbitrary measure equality is assumed.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaRssAdmissibleCorrection
open LeanFormal.IUT.N8Closure.EtaGlobalRssAtF
open LeanFormal.IUT.N8Closure.EtaQOClassGlobalActual
open LeanFormal.IUT.LocalFieldIntegralUnits

namespace LeanFormal.IUT.N8Closure.EtaQOReadoutRelationActual

universe u v

/-- If two additive Haar measures agree at an open set and are normalized there,
their common Haar scalar factor is 1, hence they agree on every everywhere
positive measurable set. -/
theorem normalized_haar_agree_on_everywherePos
    {G : Type v} [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (μ' μ : Measure G) [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure]
    {O : Set G} (hO : IsOpen O) (hμO : μ O = 1) (hμ'O : μ' O = 1)
    {s : Set G} (hs : MeasurableSet s) (hpos : μ.IsEverywherePos s) :
    μ' s = μ s := by
  have hOeq := MeasureTheory.Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen
    (μ' := μ') (μ := μ) hO
  have hscalar : μ'.addHaarScalarFactor μ = 1 := by
    rw [hμO, hμ'O] at hOeq
    -- hOeq : 1 = scalar • 1
    simpa using hOeq.symm
  have hseq := MeasureTheory.Measure.measure_isAddHaarMeasure_eq_smul_of_isEverywherePos
    (μ' := μ') (μ := μ) hs hpos
  rw [hscalar] at hseq
  simpa using hseq

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (K X)] [BorelSpace (K X)]
variable (μK : Measure (K X)) [Measure.IsAddHaarMeasure μK]
variable [Measure.IsOpenPosMeasure μK] [IsFiniteMeasureOnCompacts μK]
variable [ProperSpace (K X)] [IsUltrametricDist (K X)]
variable [NormedSpace ℚ_[FPlacePrime X] (K X)]
variable [FiniteDimensional ℚ_[FPlacePrime X] (K X)]
variable [Nontrivial (K X)]
variable [NormSMulClass ℚ_[FPlacePrime X] (K X)]

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable (μQ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μQ]

/-- Canonical integral-unit ball at K. -/
def O_K : Set (K X) := Integers (K X)

/-- Canonical integral-unit ball at QCompletion. -/
def O_Q : Set (QCompletion X) := Integers (QCompletion X)

/-- Missing actual normalizations of the canonical GlobalRssAtF measure and the
multiradial QCompletion Haar measure at the integral-unit balls. -/
def NormalizationInputs : Prop :=
  μK (O_K X) = 1 ∧ μQ (O_Q X) = 1

end LeanFormal.IUT.N8Closure.EtaQOReadoutRelationActual
