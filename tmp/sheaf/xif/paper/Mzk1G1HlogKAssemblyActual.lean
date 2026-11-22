/- hlogK (ii) 部分（paper IV L1424 F 版）:
  (a) tower 恒等式: logDifferentK − logDifferentF = (1/[K:Q])·log N(diff K/F);
  (b) per-p conductorDifference ≤ differentTerm 的有限和版本;
  (c) 接口: 若相对 different 有上界 log N(diff) ≤ [K:Q](log f_F + 2 log l)
      （paper L1424 的全局上界，当前作为 hstepVIII 显式中间义务），则 hlogK。

  全局上界本身需要 Prop1.3(ii) 的 DVR donor
  (IUTIV.Estimates.DifferentDegreeUpperBound.iutIVProp13ii_normalizedDifferent_le)
  的 localization 实例化，派 emmy 并行做；本文件不 fake 它。 -/
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1HT82DiscrAssemblyActual
import tmp.sheaf.xif.paper.Mzk1G1LocalConductorInhabitantActual
import tmp.sheaf.xif.paper.Mzk1ULBadFPrimeSetActual

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1G1HlogKAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1HT82DiscrAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1G1LocalConductorInhabitantActual
open LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual
open NumberField

universe u

/-- tower 恒等式: logDifferentK − logDifferentF = (1/[K:Q])·log N(diff K/F)。 -/
theorem logDifferentK_sub_logDifferentF_eq
    {F : Type u} [Field F] [NumberField F]
    {K : Type u} [Field K] [NumberField K] [Algebra F K]
    [Module.Finite (𝓞 F) (𝓞 K)] :
    Real.log (NumberField.rootDiscr K) - Real.log (NumberField.rootDiscr F) =
      Real.log ((Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 K)) : ℕ) : ℝ) /
        (Module.finrank ℚ K : ℝ) := by
  have h := log_rootDiscr_eq_add (K := F) (L := K)
  linarith

/-- hlogK 的接口: 相对 different 上界 ⇒ paper L1424 的 F 版 hlogK。 -/
theorem hlogK_of_relative_different_bound
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (hbound : Real.log
        ((Ideal.absNorm (differentIdeal (𝓞 T.arithmetic.F) (𝓞 T.arithmetic.K)) : ℕ) : ℝ) ≤
      (Module.finrank ℚ T.arithmetic.K : ℝ) *
        (logConductorFActual T + 2 * Real.log (l.value : ℝ))) :
    Real.log (NumberField.rootDiscr T.arithmetic.K) ≤
      Real.log (NumberField.rootDiscr T.arithmetic.F) +
        logConductorFActual T + 2 * Real.log (l.value : ℝ) := by
  have h := logDifferentK_sub_logDifferentF_eq (F := T.arithmetic.F) (K := T.arithmetic.K)
  have hpos : (0 : ℝ) < (Module.finrank ℚ T.arithmetic.K : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hdiv : Real.log
      ((Ideal.absNorm (differentIdeal (𝓞 T.arithmetic.F) (𝓞 T.arithmetic.K)) : ℕ) : ℝ) /
        (Module.finrank ℚ T.arithmetic.K : ℝ) ≤
      logConductorFActual T + 2 * Real.log (l.value : ℝ) := by
    rw [div_le_iff₀ hpos]
    linarith
  linarith

/-- 𝓞F 的极大非零理想索引类型。 -/
def maxIdealF (F : Type u) [Field F] [NumberField F] : Type u :=
  {p : Ideal (𝓞 F) // p.IsMaximal ∧ p ≠ ⊥}

/-- maxIdealF 元素的 IsMaximal 实例（供 localConductorData 使用）。 -/
instance maxIdealF_isMaximal (F : Type u) [Field F] [NumberField F]
    (p : maxIdealF F) : p.1.IsMaximal := p.2.1

/-- per-p conductor 差 ≤ different 项的有限和版本。 -/
theorem sum_local_conductorDifference_le
    (F : Type u) [Field F] [NumberField F]
    (K : Type u) [Field K] [NumberField K] [Algebra F K]
    [Module.Finite (𝓞 F) (𝓞 K)] (s : Finset (maxIdealF F)) :
    (∑ p ∈ s, conductorDifference (localConductorData (F := F) (K := K) p.1 p.2.2)) ≤
      (∑ p ∈ s, differentTerm (localConductorData (F := F) (K := K) p.1 p.2.2)) := by
  apply Finset.sum_le_sum
  intro p _
  exact localConductorData_conductorDifference_le (F := F) (K := K) p.1 p.2.2

end LeanFormal.IUT.XiFPaper.Mzk1G1HlogKAssemblyActual