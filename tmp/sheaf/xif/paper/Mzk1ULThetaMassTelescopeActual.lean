/- J1 per-b 质量望远镜（Lead J1 方案 Σ 步）:
  MpaperB b = (1/(2l))·(1/[Fmod:Q])·ord_b·logp_b
  given hsum: Σ_{P|b} f_P·c_P = [F:Fmod]·ord_b（ord tower 的直接结论）
  与 hlog: 所有 P|b 的 log p_P = logp_b（同一有理素数的 residue log）;
  finrank 塔 [F:Q]=[F:Fmod]·[Fmod:Q]。 -/
import tmp.sheaf.xif.paper.Mzk1ULOrdFiberTowerActual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULThetaMassTelescopeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1ULOrdFiberTowerActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- 塔恒等式 [F:Q]=[F:Fmod][Fmod:Q]。 -/
theorem finrank_F_eq_mul (T : SourceNativeInitialThetaData.{0} l) :
    (Module.finrank ℚ (T.arithmetic.F) : ℝ) =
      (Module.finrank (T.arithmetic.Fmod) (T.arithmetic.F) : ℝ) *
        (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) := by
  have h : Module.finrank (T.arithmetic.Fmod) (T.arithmetic.F) *
      Module.finrank ℚ (T.arithmetic.Fmod) = Module.finrank ℚ (T.arithmetic.F) := by
    rw [mul_comm]
    exact Module.finrank_mul_finrank ℚ (T.arithmetic.Fmod) (T.arithmetic.F)
  exact_mod_cast h

/-- per-b 质量望远镜。 -/
theorem MpaperB_eq_ordB
    (b : Bad (nativePlaceSelection T)) (ordB logp : ℝ)
    (hsum : (∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      (x.1.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b x.1 x.2 : ℝ)) =
      (Module.finrank (T.arithmetic.Fmod) (T.arithmetic.F) : ℝ) * ordB)
    (hlog : ∀ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : ℝ) = logp) :
    MpaperB (l := l) T b =
      (1 / (2 * (l.value : ℝ))) * (1 / (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ)) *
        ordB * logp := by
  unfold MpaperB
  have hFQ : (Module.finrank ℚ (T.arithmetic.F) : ℝ) =
      (Module.finrank (T.arithmetic.Fmod) (T.arithmetic.F) : ℝ) *
        (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) := finrank_F_eq_mul T
  have hsumlog : (∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      (x.1.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b x.1 x.2 : ℝ) *
        Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : ℝ)) =
      (∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      (x.1.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b x.1 x.2 : ℝ)) * logp := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hlog x hx]
  rw [hsumlog, hsum, hFQ]
  field_simp
  ring

end LeanFormal.IUT.XiFPaper.Mzk1ULThetaMassTelescopeActual