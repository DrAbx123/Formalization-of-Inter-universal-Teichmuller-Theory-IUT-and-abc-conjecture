/- L2+L3 scaffold: local support inequality (Prop1.3(i)) + summation identity => 2*d_mod bound.
   All unproven steps are explicit fields/Props (no fake); locals come from L1 (Mzk1ULHbadLocalLogActual).
   - L2: per vQ: localLogS vQ <= 2*(localLogD vQ + localLogF vQ) (named obligation prop13_local_support);
   - term: log p <= localLogS p;
   - L3: Sum_{vQ in dst} localLogD = d_mod*logD, Sum localLogF = d_mod*logF;
   => Sum_{vQ} log p <= 2*d_mod*(logD+logF). -/
import tmp.sheaf.xif.paper.Mzk1ULHSQLambdaNumericTruncActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadLocalSupportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericTruncActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- L1/L2/L3 的局部数据（每 vQ∈V(Q)^dst）: s/d/f 的 deg_E 局部量 + per-place 界 + 求和恒等。
    字段即具名义务; 构造由 L1 (fiber deg) + emmy localization + Prop1.3(i) 填。 -/
structure LocalSupportData (lam : ℂ) (hlam : IsAlgebraic ℚ lam) where
  localLogS : ℕ → ℝ
  localLogD : ℕ → ℝ
  localLogF : ℕ → ℝ
  logD : ℝ
  logF : ℝ
  dmod : ℝ
  /-- term-wise: log p <= localLogS p (p in dst)。 -/
  hterm : ∀ (p : ℕ), Real.log (p : ℝ) ≤ localLogS p
  /-- L2: Prop1.3(i) per-place support bound (named obligation prop13_local_support)。 -/
  hlocal : ∀ (p : ℕ), localLogS p ≤ 2 * (localLogD p + localLogF p)
  /-- L3: Sum_{p in dst} localLogD p = d_mod * logD。 -/
  hsumD : (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, localLogD p) = dmod * logD
  /-- L3: Sum localLogF = d_mod * logF。 -/
  hsumF : (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, localLogF p) = dmod * logF

/-- L2: per-vQ 求和 => primorial 的截断 union 界 2*d_mod*(logD+logF)（真推导，inputs 为字段）。 -/
theorem local_sum_bound {lam : ℂ} {hlam : IsAlgebraic ℚ lam}
    (D : LocalSupportData (T := T) lam hlam) :
    (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      2 * (D.dmod * D.logD + D.dmod * D.logF) := by
  have h1 : (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, D.localLogS p) :=
    Finset.sum_le_sum (fun p _ => D.hterm p)
  have h2 : (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, D.localLogS p) ≤
      (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T,
        2 * (D.localLogD p + D.localLogF p)) :=
    Finset.sum_le_sum (fun p _ => D.hlocal p)
  have h3 : (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, D.localLogD p) +
      (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, D.localLogF p) =
      D.dmod * D.logD + D.dmod * D.logF := by
    rw [D.hsumD, D.hsumF]
  have h4 : (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T,
          (D.localLogD p + D.localLogF p)) =
      (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, D.localLogD p) +
        (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, D.localLogF p) :=
    Finset.sum_add_distrib
  calc (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ))
      ≤ (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, D.localLogS p) := h1
    _ ≤ (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T,
          2 * (D.localLogD p + D.localLogF p)) := h2
    _ = 2 * ((∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, D.localLogD p) +
          (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, D.localLogF p)) := by
          rw [← Finset.mul_sum, h4]
    _ = 2 * (D.dmod * D.logD + D.dmod * D.logF) := by rw [h3]

#print axioms local_sum_bound

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadLocalSupportActual