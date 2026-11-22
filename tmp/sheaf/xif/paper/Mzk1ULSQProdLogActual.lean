/- s^Q 的乘积-log 形式（接 Mzk1HTF3ConductorHeightActual 的 TODO）:
  Real.log (∏ P∈S, ((underIntGen P).natAbs : ℝ)) = Σ P∈S, Real.log ((underIntGen P).natAbs : ℝ)。
  donor: Mzk1HT82PaperWeightDiffActual.underIntGen（P.under ℤ 的生成元）;
  Mzk1ULTripodalConductorActual.sQOf/log_sQOf_eq（DONE 23:55:17）用于 distinct rational primes 口径。 -/
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import tmp.sheaf.xif.paper.Mzk1ULTripodalConductorActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSQProdLogActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalConductorActual

universe u

/-- 乘积 log 分解（族 S 上，每项 natAbs 非零）。 -/
theorem log_prod_underIntGen_eq_sum
    {K : Type u} [Field K] [NumberField K]
    (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, underIntGen (K := K) P ≠ 0) :
    Real.log (∏ P ∈ S, ((underIntGen (K := K) P).natAbs : ℝ)) =
      ∑ P ∈ S, Real.log ((underIntGen (K := K) P).natAbs : ℝ) := by
  apply Real.log_prod
  intro P hP
  exact Int.cast_ne_zero.mpr (Int.natAbs_ne_zero.mpr (hS P hP))

/-- distinct rational primes 的 primorial 口径（与 sQOf 一致）:
  log s^Q = Σ_{p∈S} log p（与 paper L1485-1501 的 distinct primes 定义一致）。 -/
theorem log_sQOf_eq_sum (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 0) :
    Real.log (sQOf S : ℝ) = ∑ p ∈ S, Real.log (p : ℝ) :=
  log_sQOf_eq S hS

#print axioms log_prod_underIntGen_eq_sum
#print axioms log_sQOf_eq_sum

end LeanFormal.IUT.XiFPaper.Mzk1ULSQProdLogActual
