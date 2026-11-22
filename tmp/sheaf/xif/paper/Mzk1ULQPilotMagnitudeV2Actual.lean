/- Q_paper 的 paper-faithful 全 fiber 版本 qPilotMagnitudePaper_v2（owner david）。

paper: log q := deg(q^ADiv)（IUT IV L1324-1333）; Def 1.9 normalized degree（L1206-1235）;
deg(a|K)=deg(a)（L977-1000）⇒ log q = (1/[F:Q])Σ_{v∈V(F)^bad} c_v f_v log p_v。
当前 qPilotMagnitudePaper 用选定 F-lift 的 order + K-lift 权（混合、单 lift），非 paper; 本文件用
bad F-places 全 fiber（primesOverFinset，见 Mzk1ULBadFPrimeSetActual 的结论）逐位构造 q-candidate。

LEGACY: Mzk1URThetaKSideActual.qPilotMagnitudePaper 保留作旧口径审计，不进 C4/hP5 主链。 -/
import Mathlib.Tactic
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.Mzk1ULBadFPrimeSetActual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceQCandidate
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open NumberField
open scoped BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- 任意 F-位（comap 到已知 bad moduli 位）上的 q-candidate。 -/
noncomputable def qVFamAt (p : NumberField.FinitePlace T.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) p ∈
      (nativePlaceSelection T).V_mod_bad) :
    FinitePlaceQCandidate p :=
  (Classical.choice (T.clauseB.q_comparison p hp)).parameter

/-- P ∈ primesOverFinset 对应一个 F-位。 -/
noncomputable def badFPlaceOfIdeal {b : Bad (nativePlaceSelection T)}
    (P : Ideal (𝓞 (T.arithmetic.F)))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))) :
    NumberField.FinitePlace T.arithmetic.F := by
  haveI : (b.1.maximalIdeal.asIdeal).IsMaximal := b.1.maximalIdeal.isMaximal
  have hp0 : b.1.maximalIdeal.asIdeal ≠ ⊥ := b.1.maximalIdeal.ne_bot
  have hmem : P ∈ Ideal.primesOver (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F)) :=
    (IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 (T.arithmetic.F)) hp0).mp hP
  have hne : P ≠ ⊥ := by
    intro hbot
    have hunder : P.under (𝓞 (T.arithmetic.Fmod)) = ⊥ := by simp [hbot]
    have hp_eq : b.1.maximalIdeal.asIdeal = P.under (𝓞 (T.arithmetic.Fmod)) := hmem.2.over
    rw [hunder] at hp_eq
    exact hp0 hp_eq
  exact NumberField.FinitePlace.mk
    { asIdeal := P
      isPrime := hmem.1
      ne_bot := hne }

/-- badFPlaceOfIdeal 的 comap 是 b.1。 -/
theorem badFPlaceOfIdeal_comap {b : Bad (nativePlaceSelection T)}
    (P : Ideal (𝓞 (T.arithmetic.F)))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))) :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (badFPlaceOfIdeal T P hP) = b.1 := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  change (NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (badFPlaceOfIdeal T P hP)).maximalIdeal.asIdeal =
    b.1.maximalIdeal.asIdeal
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  -- (badFPlaceOfIdeal).maximalIdeal.asIdeal = P
  haveI : (b.1.maximalIdeal.asIdeal).IsMaximal := b.1.maximalIdeal.isMaximal
  have hp0 : b.1.maximalIdeal.asIdeal ≠ ⊥ := b.1.maximalIdeal.ne_bot
  have hmem : P ∈ Ideal.primesOver (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F)) :=
    (IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 (T.arithmetic.F)) hp0).mp hP
  have hlie : P.LiesOver b.1.maximalIdeal.asIdeal := hmem.2
  have hMk : (badFPlaceOfIdeal T P hP).maximalIdeal.asIdeal = P := by
    unfold badFPlaceOfIdeal
    rw [NumberField.FinitePlace.maximalIdeal_mk]
  rw [hMk]
  exact hlie.over.symm


/-- 选定 b 与 P（P over b.1）后，F-place 上的 q-candidate order c_P。 -/
noncomputable def orderAtFPlace (b : Bad (nativePlaceSelection T))
    (P : Ideal (𝓞 (T.arithmetic.F)))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))) : ℕ :=
  (qVFamAt T (badFPlaceOfIdeal T P hP) (by
    rw [badFPlaceOfIdeal_comap T P hP]
    exact b.2)).order

/-- **paper-faithful Q**: (1/[F:Q])·Σ_b Σ_{P over b.1} f_P·c_P·log p_P（全 fiber，无单 lift 混合）。 -/
noncomputable def qPilotMagnitudePaper_v2 : ℝ :=
  (∑ b : Bad (nativePlaceSelection T),
      ∑ x ∈ (IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
        ((x.1.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b x.1 x.2 : ℝ) *
          Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : ℝ))) /
    (Module.finrank ℚ (T.arithmetic.F) : ℝ)

/-- qPilotMagnitudePaper_v2 非负。 -/
theorem zero_le_qPilotMagnitudePaper_v2 : 0 ≤ qPilotMagnitudePaper_v2 (T := T) := by
  unfold qPilotMagnitudePaper_v2
  have hsum : 0 ≤ ∑ b : Bad (nativePlaceSelection T),
      ∑ x ∈ (IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
        ((x.1.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b x.1 x.2 : ℝ) *
          Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : ℝ)) := by
    apply Finset.sum_nonneg
    intro b _
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rcases Nat.eq_zero_or_pos ((underIntGen (K := T.arithmetic.F) x.1).natAbs) with h0 | hpos
      · simp [h0]
      · exact Real.log_nonneg (by exact_mod_cast hpos)
  have hfr : (0 : ℝ) < (Module.finrank ℚ (T.arithmetic.F) : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := T.arithmetic.F)
  exact div_nonneg hsum hfr.le

/-- paper M = Q/(2l)。 -/
noncomputable def M_paper_v2 : ℝ :=
  qPilotMagnitudePaper_v2 (T := T) / (2 * (l.value : ℝ))

/-- M_paper_v2 非负。 -/
theorem zero_le_M_paper_v2 : 0 ≤ M_paper_v2 (T := T) := by
  unfold M_paper_v2
  have hl : (0 : ℝ) < 2 * (l.value : ℝ) := by
    have := l.prime.pos
    positivity
  exact div_nonneg (zero_le_qPilotMagnitudePaper_v2 (T := T)) hl.le


end LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual