/- 权字典（route §5.4 / paper IUT IV Step(v),(viii)）:

λ_v := [Fmod_v : Q_p] = e_v·f_v（v ∈ V(F_mod)）; d_mod := [Fmod : Q];
H_pkt := (1/d_mod) Σ_{vQ} Σ_{v|vQ} λ_v·V_v（= Σ_{vQ} Σ_{v|vQ} (λ_v/d_mod)·V_v）。

对应: Mzk1ULWeightedHullActual.ulDivisorWeight = λ_v; ulNormalizedWeight = λ_v/Σλ;
packet 索引覆盖 fiber 全部 places 时 Σλ = 局部总度，ulNormalizedWeight 即 λ/d_mod。

Q/M/D 槽用 f 权（Def 1.9 normalized degree）: Q = qPilotMagnitudePaper_v2（f_P/[F:Q] 权），
M = Q/(2l)，与 λ 权槽分开（paper IV L462-463 vs L1705-1743/L1860-1878）。

本文件只给接口陈述（定义/等式/非负/和为1），不重证 C1。 -/
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1ULWeightedHullActual
import tmp.sheaf.xif.paper.Mzk1ULHpktActual
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1ULFBadPlaceIndexActual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULWeightDictionaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ULWeightedHullActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1ULFBadPlaceIndexActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open NumberField

universe u

/-- paper λ_v = [Fmod_v : Q_p] 定义展开（= ulDivisorWeight）。 -/
theorem paperLambda_eq_ulDivisorWeight
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime K p) :
    (Module.finrank ℚ_[p] (CommonPrimeCompletion place) : ℝ) =
      ulDivisorWeight (K := K) (p := p) place := rfl

/-- H_pkt 局部权 λ_v/d_mod 的 fiber 归一形式。 -/
theorem paperHpktWeight_eq_normalized
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type u} [Fintype ι] (places : ι → Unit → FinitePlaceAtPrime K p)
    (tuple : ι → Unit) (i : ι) :
    ulNormalizedWeight (p := p) places tuple i =
      ulPlaceWeight (p := p) places tuple i /
        ∑ j, ulPlaceWeight (p := p) places tuple j := rfl

/-- λ 权归一: Σ_i λ_i/Σλ = 1。 -/
theorem paperHpktWeight_sum_one
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type u} [Fintype ι] (places : ι → Unit → FinitePlaceAtPrime K p)
    (tuple : ι → Unit)
    (hpos : 0 < ∑ i, ulPlaceWeight (p := p) places tuple i) :
    (∑ i, ulNormalizedWeight (p := p) places tuple i) = 1 :=
  ulNormalizedWeight_sum (p := p) places tuple hpos

/-- H_pkt = (1/Σλ)·Σ_i λ_i·V_i（λ 权形式）。 -/
theorem hpkt_lambda_form
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type u} [Fintype ι] (places : ι → Unit → FinitePlaceAtPrime K p)
    (tuple : ι → Unit) (V : ι → ℝ) :
    (∑ i, ulNormalizedWeight (p := p) places tuple i * V i) =
      (1 / ∑ i, ulPlaceWeight (p := p) places tuple i) *
        ∑ i, ulPlaceWeight (p := p) places tuple i * V i := by
  unfold ulNormalizedWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-- Q/M 槽的 f 权与 λ 权是不同族: BadF 的 fPlaceWeight 是 Def1.9 的 f_P/[F:Q]。 -/
theorem qSlot_fWeight_eq
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (x : BadF T) :
    fPlaceWeight T x = paperDifferentWeight T.arithmetic.F x.1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ULWeightDictionaryActual