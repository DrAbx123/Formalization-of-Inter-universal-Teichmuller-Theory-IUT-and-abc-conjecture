/- Route 8.5 (F7): explicit Fermat-lift number field.

Reuse / 查重:
* No existing `fermatLift` field in tmp/sheaf/xif/paper (grep 0; AG_FLT_* only curve/Cech pieces).
* Mathlib donors: `IsAlgClosed.exists_root`, `Polynomial.degree_X_pow_sub_C`,
  `IntermediateField.adjoin.finrank`, `Module.finrank_mul_finrank`, `adjoin_adjoin_left`.
Plan (lead-approved): x = (a/c)^(1/n), y = (b/c)^(1/n) in an algebraic closure,
L = Q(x,y); [L:Q] <= n^2.
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F7LiftActual

open Polynomial IntermediateField

/-- A chosen n-th root of q in an algebraic closure of Q. -/
noncomputable def fermatRoot (n : ℕ) (hn : 0 < n) (q : ℚ) : AlgebraicClosure ℚ :=
  Classical.choose (IsAlgClosed.exists_root
    ((X : (AlgebraicClosure ℚ)[X]) ^ n - C (algebraMap ℚ (AlgebraicClosure ℚ) q))
    (by rw [degree_X_pow_sub_C hn (algebraMap ℚ (AlgebraicClosure ℚ) q)];
        exact Nat.cast_ne_zero.mpr hn.ne'))

variable (n : ℕ) (hn : 0 < n) (q : ℚ)

/-- The defining property of the chosen root. -/
theorem fermatRoot_pow : (fermatRoot n hn q) ^ n = algebraMap ℚ (AlgebraicClosure ℚ) q := by
  have h := Classical.choose_spec (IsAlgClosed.exists_root
    ((X : (AlgebraicClosure ℚ)[X]) ^ n - C (algebraMap ℚ (AlgebraicClosure ℚ) q))
    (by rw [degree_X_pow_sub_C hn (algebraMap ℚ (AlgebraicClosure ℚ) q)];
        exact Nat.cast_ne_zero.mpr hn.ne'))
  have h' : (fermatRoot n hn q) ^ n - algebraMap ℚ (AlgebraicClosure ℚ) q = 0 := by
    dsimp [fermatRoot]
    rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at h
    simpa using h
  exact sub_eq_zero.mp h'

/-- A polynomial relation transport: q = a/c. -/
noncomputable def fermatLiftL (a b c : ℕ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ
    ({fermatRoot n hn ((a : ℚ) / c), fermatRoot n hn (1 - (a : ℚ) / c)} : Set (AlgebraicClosure ℚ))

/-- Membership of the first lift coordinate. -/
theorem fermatLiftL_x_mem (a b c : ℕ) :
    fermatRoot n hn ((a : ℚ) / c) ∈ fermatLiftL n hn a b c := by
  unfold fermatLiftL
  apply subset_adjoin
  exact Set.mem_insert _ _

/-- Membership of the second lift coordinate. -/
theorem fermatLiftL_y_mem (a b c : ℕ) :
    fermatRoot n hn (1 - (a : ℚ) / c) ∈ fermatLiftL n hn a b c := by
  unfold fermatLiftL
  apply subset_adjoin
  exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

/-- x^n + y^n = 1 for a Fermat-type pair, where y^n = 1 - a/c and x^n = a/c. -/
theorem fermatLift_x_pow_add_y_pow (a b c : ℕ) (hfermat : ((b : ℚ) / c) ^ n = 1 - ((a : ℚ) / c) ^ n) :
    (fermatRoot n hn ((a : ℚ) / c)) ^ n + (fermatRoot n hn (1 - ((a : ℚ) / c))) ^ n = 1 := by
  rw [fermatRoot_pow n hn ((a : ℚ) / c), fermatRoot_pow n hn (1 - ((a : ℚ) / c))]
  simp [map_sub, map_one]

/-- Degree bound [Q(x):Q] <= n: x is a root of the monic polynomial X^n - q. -/
theorem finrank_adjoin_simple_le (q : ℚ) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ
      ({fermatRoot n hn q} : Set (AlgebraicClosure ℚ))) ≤ n := by
  have hx : IsIntegral ℚ (fermatRoot n hn q) :=
    IsIntegral.of_pow hn (by rw [fermatRoot_pow]; exact isIntegral_algebraMap)
  rw [IntermediateField.adjoin.finrank hx]
  have hroot : aeval (fermatRoot n hn q)
      ((X : ℚ[X]) ^ n - C q) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, fermatRoot_pow, sub_self]
  have hmonic : ((X : ℚ[X]) ^ n - C q).Monic := monic_X_pow_sub_C q hn.ne'
  exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ _ hroot) hmonic.ne_zero).trans_eq
    natDegree_X_pow_sub_C

#print axioms fermatRoot_pow
end LeanFormal.IUT.XiFPaper.Mzk1G1F7LiftActual
