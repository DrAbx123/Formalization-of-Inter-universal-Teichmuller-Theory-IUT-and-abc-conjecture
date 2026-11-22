import tmp.sheaf.xif.paper.Mzk1G1F7LiftActual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic
/-!
# F7 basic: `fermatLiftL` finite-dimensional and a `NumberField`

Route §9.1: L584/L586/L594/L602/L613.  Stable small file with the three green facts;
`[L:Q]≤n²` and the generic singleton-degree lemma live in `Mzk1G1F7LiftTowerActual`.
-/
noncomputable section
open Polynomial IntermediateField
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F7LiftDegreeBasicActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F7LiftActual

variable (n : ℕ) (hn : 0 < n) (a b c : ℕ)

theorem isIntegral_fermatRoot (q : ℚ) : IsIntegral ℚ (fermatRoot n hn q) :=
  IsIntegral.of_pow hn (by rw [fermatRoot_pow n hn q]; exact isIntegral_algebraMap)

theorem fermatLiftL_finiteDimensional : FiniteDimensional ℚ (fermatLiftL n hn a b c) := by
  unfold fermatLiftL
  refine IntermediateField.finiteDimensional_adjoin (K := ℚ)
    (S := ({fermatRoot n hn ((a : ℚ) / c),
      fermatRoot n hn (1 - (a : ℚ) / c)} : Set (AlgebraicClosure ℚ))) ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact isIntegral_fermatRoot n hn ((a : ℚ) / c)
  · exact isIntegral_fermatRoot n hn (1 - (a : ℚ) / c)

noncomputable instance fermatLiftL_numberField : NumberField (fermatLiftL n hn a b c) := by
  haveI := fermatLiftL_finiteDimensional n hn a b c
  haveI : CharZero (fermatLiftL n hn a b c) := by infer_instance
  exact ⟨⟩


theorem finrank_adjoin_singleton_le_of_pow_eq {K L : Type*} [Field K] [Field L]
    [Algebra K L] (y : L) (m : ℕ) (hm : 0 < m) (q : K) (hy : y ^ m = algebraMap K L q) :
    Module.finrank K (IntermediateField.adjoin K ({y} : Set L)) ≤ m := by
  have hyint : IsIntegral K y :=
    IsIntegral.of_pow hm (by rw [hy]; exact isIntegral_algebraMap)
  rw [IntermediateField.adjoin.finrank hyint]
  have hroot : Polynomial.aeval y ((Polynomial.X : K[X]) ^ m - Polynomial.C q) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hy, sub_self]
  have hmonic : ((Polynomial.X : K[X]) ^ m - Polynomial.C q).Monic :=
    Polynomial.monic_X_pow_sub_C q hm.ne'
  have hdvd := minpoly.dvd K y hroot
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hmonic.ne_zero
  rw [Polynomial.natDegree_X_pow_sub_C] at hdeg
  exact hdeg

set_option maxHeartbeats 1000000 in
theorem fermatLiftL_finrank_le_sq : Module.finrank ℚ (fermatLiftL n hn a b c) ≤ n * n := by
  let x : AlgebraicClosure ℚ := fermatRoot n hn ((a : ℚ) / c)
  let y : AlgebraicClosure ℚ := fermatRoot n hn (1 - (a : ℚ) / c)
  let Kx : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ ({x} : Set (AlgebraicClosure ℚ))
  have hL : fermatLiftL n hn a b c =
      (IntermediateField.adjoin Kx ({y} : Set (AlgebraicClosure ℚ))).restrictScalars ℚ := by
    unfold fermatLiftL
    rw [show ({x, y} : Set (AlgebraicClosure ℚ)) = ({x} : Set (AlgebraicClosure ℚ)) ∪ {y} by
      ext z; simp [or_comm]]
    rw [← IntermediateField.adjoin_adjoin_left (F := ℚ)
      (S := ({x} : Set (AlgebraicClosure ℚ))) (T := ({y} : Set (AlgebraicClosure ℚ)))]
    rfl
  have hy : y ^ n = algebraMap Kx (AlgebraicClosure ℚ) (algebraMap ℚ Kx (1 - (a : ℚ) / c)) := by
    rw [fermatRoot_pow n hn (1 - (a : ℚ) / c)]
    exact (IsScalarTower.algebraMap_apply ℚ Kx (AlgebraicClosure ℚ) (1 - (a : ℚ) / c)).symm
  have h1 : Module.finrank Kx (IntermediateField.adjoin Kx ({y} : Set (AlgebraicClosure ℚ))) ≤ n :=
    finrank_adjoin_singleton_le_of_pow_eq (K := Kx) y n hn
      (algebraMap ℚ Kx (1 - (a : ℚ) / c)) hy
  have h2 : Module.finrank ℚ Kx ≤ n := finrank_adjoin_simple_le n hn ((a : ℚ) / c)
  rw [hL]
  change Module.finrank ℚ (IntermediateField.adjoin Kx ({y} : Set (AlgebraicClosure ℚ))) ≤ n * n
  rw [← Module.finrank_mul_finrank ℚ Kx (IntermediateField.adjoin Kx ({y} : Set (AlgebraicClosure ℚ)))]
  exact Nat.mul_le_mul h2 h1

#print axioms finrank_adjoin_singleton_le_of_pow_eq
#print axioms fermatLiftL_finrank_le_sq
#print axioms fermatLiftL_finiteDimensional
#print axioms fermatLiftL_numberField
end LeanFormal.IUT.XiFPaper.Mzk1G1F7LiftDegreeBasicActual
end