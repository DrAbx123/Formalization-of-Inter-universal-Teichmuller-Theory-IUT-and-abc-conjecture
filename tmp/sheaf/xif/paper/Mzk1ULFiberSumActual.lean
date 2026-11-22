/- fibre Σef 计数（kurt 用于吸收 v2 的其余 lift 项）:
  Mathlib sum_ramification_inertia (Basic.lean:585):
    ∑_{P ∈ primesOverFinset p S} ramificationIdx' p P * inertiaDeg' p P = finrank (Frac S) (Frac R)。
  实例化 R := 𝓞 Fmod, S := 𝓞 F, p := b.1.maximalIdeal.asIdeal。 -/
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1HT82UnderIntGenQVActual
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULFiberSumActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- fiber 内的 Σ e_P f_P = [F:Fmod]（相对 ramification/inertia）。 -/
theorem fiber_sum_ef (b : Bad (nativePlaceSelection T)) :
    (∑ P ∈ IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F)),
      Ideal.ramificationIdx' (b.1.maximalIdeal.asIdeal) P *
        Ideal.inertiaDeg' (b.1.maximalIdeal.asIdeal) P) =
      Module.finrank (T.arithmetic.Fmod) (T.arithmetic.F) := by
  haveI : (b.1.maximalIdeal.asIdeal).IsMaximal := b.1.maximalIdeal.isMaximal
  exact Ideal.sum_ramification_inertia (S := 𝓞 (T.arithmetic.F))
    (K := T.arithmetic.Fmod) (L := T.arithmetic.F)
    (p := b.1.maximalIdeal.asIdeal) (hp0 := b.1.maximalIdeal.ne_bot)

/-- v2 的 fibre 展开（rfl）：Σ_b Σ_{P} f_P c_P logp / [F:Q]。 -/
theorem qPilotMagnitudePaper_v2_expand :
    qPilotMagnitudePaper_v2 (T := T) =
      (∑ b : Bad (nativePlaceSelection T),
        ∑ x ∈ (IsDedekindDomain.primesOverFinset
            (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
          ((x.1.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b x.1 x.2 : ℝ) *
            Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : ℝ))) /
        (Module.finrank ℚ (T.arithmetic.F) : ℝ) := rfl

#print axioms fiber_sum_ef
#print axioms qPilotMagnitudePaper_v2_expand

end LeanFormal.IUT.XiFPaper.Mzk1ULFiberSumActual