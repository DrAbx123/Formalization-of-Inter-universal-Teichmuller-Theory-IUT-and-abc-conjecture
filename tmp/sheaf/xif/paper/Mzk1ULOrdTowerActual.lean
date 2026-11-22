/- ord tower（理想层）: localOrderAt 的乘性/幂性 + 映射下 ord_P(map I)=e_P·ord_b(I) 的幂特例。
  donor: normalizedFactors_mul/pow (NormalizedFactors:143/165), Multiset.count_add (AddSub:124),
  Ideal.map_pow (Maps:665), ramificationIdx'_eq_normalizedFactors_count (Ramification:257)。 -/
import tmp.sheaf.xif.paper.Mzk1ULLocalOrderActual
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.Mzk1ULOrdTowerActual

open NumberField
open UniqueFactorizationMonoid
open LeanFormal.IUT.XiFPaper.Mzk1ULLocalOrderActual

/-- count 的 nsmul 公式。 -/
theorem count_nsmul {α : Type*} [DecidableEq α]
    (s : Multiset α) (n : ℕ) (a : α) :
    (n • s).count a = n * s.count a := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, Multiset.count_add, ih]; ring

/-- 乘性: ord_v(I·J) = ord_v(I)+ord_v(J)。 -/
theorem localOrderAt_mul {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    localOrderAt v (I * J) = localOrderAt v I + localOrderAt v J := by
  unfold localOrderAt
  rw [normalizedFactors_mul hI hJ]
  exact Multiset.count_add _ _ _

/-- 幂性: ord_v(I^n) = n·ord_v(I)。 -/
theorem localOrderAt_pow {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (n : ℕ) :
    localOrderAt v (I ^ n) = n * localOrderAt v I := by
  induction n with
  | zero =>
      have hnf : normalizedFactors (⊤ : Ideal (𝓞 K)) = 0 := by
        rw [← Ideal.one_eq_top]
        exact normalizedFactors_one
      show localOrderAt v (I ^ 0) = 0 * localOrderAt v I
      rw [pow_zero, Ideal.one_eq_top]
      simp [localOrderAt, hnf]
  | succ n ih =>
    rw [pow_succ, localOrderAt_mul v (I := I ^ n) (J := I) (pow_ne_zero n hI) hI, ih]
    ring

section Map

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable [Module.Finite (𝓞 K) (𝓞 L)]

/-- 幂特例: ord_P((b^n).map) = n·e_P（ord_P(algebraMap q)=e_P·ord_b(q) 的核心）。 -/
theorem localOrderAt_map_pow (b : NumberField.FinitePlace K) (P : NumberField.FinitePlace L)
    (hP : (P.maximalIdeal.asIdeal).LiesOver (b.maximalIdeal.asIdeal)) (n : ℕ) :
    localOrderAt P (((b.maximalIdeal.asIdeal) ^ n).map (algebraMap (𝓞 K) (𝓞 L))) =
      n * Ideal.ramificationIdx' (b.maximalIdeal.asIdeal) (P.maximalIdeal.asIdeal) := by
  haveI hPprime : (P.maximalIdeal.asIdeal).IsPrime := P.maximalIdeal.isPrime
  have hP0 : P.maximalIdeal.asIdeal ≠ ⊥ := P.maximalIdeal.ne_bot
  have hb0 : b.maximalIdeal.asIdeal ≠ ⊥ := b.maximalIdeal.ne_bot
  have hmap0 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) (b.maximalIdeal.asIdeal) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hb0
  have he : (normalizedFactors (Ideal.map (algebraMap (𝓞 K) (𝓞 L))
        (b.maximalIdeal.asIdeal))).count (P.maximalIdeal.asIdeal) =
      Ideal.ramificationIdx' (b.maximalIdeal.asIdeal) (P.maximalIdeal.asIdeal) := by
    rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0
      inferInstance hP0]
  unfold localOrderAt
  rw [Ideal.map_pow, normalizedFactors_pow, count_nsmul, he]


/-- 主理想版 ord_P(algebraMap q) = e_P·ord_b(q)：若 span{q}=b^n（n=ord_b(q)），
    则 span{algebraMap q}=map(span q)=(map b)^n，count 给 n·e_P。 -/
theorem ord_algebraMap_eq_e_mul_ord
    (b : NumberField.FinitePlace K) (P : NumberField.FinitePlace L)
    (hP : (P.maximalIdeal.asIdeal).LiesOver (b.maximalIdeal.asIdeal))
    (q : 𝓞 K) (n : ℕ) (hq : Ideal.span {q} = (b.maximalIdeal.asIdeal) ^ n) :
    localOrderAt P (Ideal.span {algebraMap (𝓞 K) (𝓞 L) q}) =
      Ideal.ramificationIdx' (b.maximalIdeal.asIdeal) (P.maximalIdeal.asIdeal) * n := by
  have hspan : Ideal.span {algebraMap (𝓞 K) (𝓞 L) q} =
      Ideal.map (algebraMap (𝓞 K) (𝓞 L)) ((b.maximalIdeal.asIdeal) ^ n) := by
    rw [← hq, Ideal.map_span]
    simp
  rw [hspan, localOrderAt_map_pow b P hP n]
  ring

end Map


#print axioms localOrderAt_mul
#print axioms localOrderAt_pow
#print axioms localOrderAt_map_pow

end LeanFormal.IUT.XiFPaper.Mzk1ULOrdTowerActual