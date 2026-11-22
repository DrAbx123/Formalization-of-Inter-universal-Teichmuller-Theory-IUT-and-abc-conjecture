/- (A) 修正: F_tpd/F 侧 conductor 的 paper 位权版本（owner david 构造; sophie 只换 SAr_tripodal 定义）。

paper 依据: IUT-TEXT IV L1305-1313（V(F)^bad = V^bad_mod ×_{V_mod} V(F); fF^ADiv 系数 1 的位除子）、
L1341-1353、Def 1.9 L1206-1235（deg(a)=(1/[F:Q])Σ c_v log q_v）⇒ log fF = (1/[F:Q])Σ_{v∈V(F)^bad} f_v log p_v。
注意: nativeBadToFPlace 只给每个 bad Fmod 位一个 lift（单射但漏位重数），故必须用
IsDedekindDomain.primesOverFinset 的全 fiber 并集（Mathlib NumberTheory/RamificationInertia/Basic:586,
RingTheory/DedekindDomain/Ideal/Lemmas:1166/1179）。

F 版 S_ar = log dF + log fF 与 paper 的 F_tpd 版差 ≤ 21（IV L1412-1426），且 F 版 ≥ F_tpd 版，
hstepVIII/hii 的 RHS 更大，不等式不会变难；+21 吸收方向须在 hii 常数 56 处再核一次（见 docstring）。 -/
import Mathlib.Tactic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import tmp.sheaf.xif.paper.Mzk1HT82AbsDifferentSumActual

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open NumberField
open scoped BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- V(F)^bad 的全部 F 素理想（每个 bad Fmod 位的全 fiber）。 -/
noncomputable def badFPrimeSet : Finset (Ideal (𝓞 (T.arithmetic.F))) :=
  (Finset.univ : Finset (Bad (nativePlaceSelection T))).biUnion (fun b =>
    letI : (b.1.maximalIdeal.asIdeal).IsMaximal := b.1.maximalIdeal.isMaximal
    IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F)))

/-- paper 的 log f_F（位权版本）: (1/[F:Q])Σ_{P∈V(F)^bad} f_P log p_P。 -/
noncomputable def logConductorFActual : ℝ :=
  (∑ P ∈ badFPrimeSet T,
      ((P.inertiaDeg ℤ : ℝ) * Real.log ((underIntGen (K := T.arithmetic.F) P).natAbs : ℝ))) /
    (Module.finrank ℚ (T.arithmetic.F) : ℝ)

/-- 每个 P ∈ badFPrimeSet: underIntGen P 的 natAbs ≥ 1（非零）。 -/
theorem underIntGen_natAbs_ge_one {P : Ideal (𝓞 (T.arithmetic.F))} (hP : P ≠ ⊥) :
    (1 : ℝ) ≤ ((underIntGen (K := T.arithmetic.F) P).natAbs : ℝ) := by
  have hunder : Ideal.span {underIntGen (K := T.arithmetic.F) P} = P.under ℤ :=
    (underIntGen_liesOver (K := T.arithmetic.F) P).over
  have hne : underIntGen (K := T.arithmetic.F) P ≠ 0 := by
    intro h0
    have hbot : (P.under ℤ) = ⊥ := by
      rw [← hunder, h0]
      simp
    exact (Ideal.under_ne_bot (A := ℤ) (P := P) hP) hbot
  have hpos : 0 < (underIntGen (K := T.arithmetic.F) P).natAbs :=
    Int.natAbs_pos.mpr hne
  have h1 : 1 ≤ (underIntGen (K := T.arithmetic.F) P).natAbs := hpos
  exact_mod_cast h1

/-- logConductorFActual 非负（每项 inertiaDeg ≥ 0, log ≥ 0, finrank > 0）。 -/
theorem zero_le_logConductorFActual : 0 ≤ logConductorFActual (T := T) := by
  unfold logConductorFActual
  have hsum : 0 ≤ ∑ P ∈ badFPrimeSet T,
      ((P.inertiaDeg ℤ : ℝ) * Real.log ((underIntGen (K := T.arithmetic.F) P).natAbs : ℝ)) := by
    apply Finset.sum_nonneg
    intro P hP
    apply mul_nonneg (Nat.cast_nonneg _)
    rcases Nat.eq_zero_or_pos ((underIntGen (K := T.arithmetic.F) P).natAbs) with h0 | hpos
    · simp [h0]
    · exact Real.log_nonneg (by exact_mod_cast hpos)
  have hfr : (0 : ℝ) < (Module.finrank ℚ (T.arithmetic.F) : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := T.arithmetic.F)
  exact div_nonneg hsum hfr.le

end LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual