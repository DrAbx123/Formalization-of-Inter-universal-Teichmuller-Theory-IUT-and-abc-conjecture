/- e=1 ⇒ delta_abs=0（Lead 2026-11-17）: Mathlib `Ideal.ramificationIdx_eq_one_iff`
   把 `P.ramificationIdx (𝓞 K) = 1` 转成 `Algebra.IsUnramifiedAt (𝓞 K) P`,
   再用 DONE donor `Mzk1G1F7DifferentExponentBoundsActual.differentExponent_eq_zero_of_unramified`。
   这样 grace 的 lambda 实例化只需给 e=1（good-reduction primes），delta=0 自动得。 -/
import tmp.sheaf.xif.paper.Mzk1G1F7DifferentExponentBoundsActual
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadUnramifiedDeltaActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1G1F7DifferentExponentBoundsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentLogActual

universe u
variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
variable [Algebra K L] [Module.Finite (𝓞 K) (𝓞 L)]
variable [Algebra.EssFiniteType (𝓞 K) (𝓞 L)] [Algebra.IsIntegral (𝓞 K) (𝓞 L)]

/-- e=1（相对 Q_p 的分歧指数） ⇒ 绝对 different 指数 delta=0。 -/
theorem delta_eq_zero_of_ramificationIdx_eq_one
    (P : Ideal (𝓞 L)) [P.IsPrime]
    [PerfectField (P.under (𝓞 K)).ResidueField]
    (h : P.ramificationIdx (𝓞 K) = 1) :
    differentExponent (K := K) (L := L) P = 0 := by
  have hunr : Algebra.IsUnramifiedAt (𝓞 K) P := by
    have hiff := Ideal.ramificationIdx_eq_one_iff (q := P) (R := (𝓞 K)) (S := (𝓞 L))
    exact hiff.mp h
  exact differentExponent_eq_zero_of_unramified (K := K) (L := L) P hunr

#print axioms delta_eq_zero_of_ramificationIdx_eq_one

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadUnramifiedDeltaActual