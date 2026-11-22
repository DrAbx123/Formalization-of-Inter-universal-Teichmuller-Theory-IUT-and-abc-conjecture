/- G1-B local ramification at the rational boundary points: at lambda = 0 (point x=0,y=1)
and lambda = 1 (point x=1,y=0) the coordinate x (resp. y) and the boundary coordinate
1-y (resp. 1-x) differ by a unit in the local ring, i.e. x^n is a unit times the uniformizer
1-y (route 3.2, the e = n algebraic core).  Requires n >= 1. -/
import tmp.sheaf.xif.paper.Mzk1G1OmegaActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaLineBundleActual
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1OmegaRamificationLocalActual

abbrev Poly : Type := MvPolynomial (Fin 2) ℚ

/-! ## The boundary point lambda = 0, i.e. (x,y) = (0,1) -/

def evalZeroOnePoly : Poly →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun i : Fin 2 => if i = 0 then 0 else 1)

@[simp] theorem evalZeroOnePoly_X0 : evalZeroOnePoly (MvPolynomial.X 0) = 0 := by
  rw [evalZeroOnePoly, MvPolynomial.eval₂Hom_X']
  simp
@[simp] theorem evalZeroOnePoly_X1 : evalZeroOnePoly (MvPolynomial.X 1) = 1 := by
  rw [evalZeroOnePoly, MvPolynomial.eval₂Hom_X']
  simp

theorem evalZeroOnePoly_fermat (n : ℕ) (hn : 1 ≤ n) : evalZeroOnePoly (fermatEquation n) = 0 := by
  rw [fermatEquation, map_sub, map_add, map_pow, map_pow, map_one, evalZeroOnePoly_X0,
    evalZeroOnePoly_X1]
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  simp [zero_pow hn0]

noncomputable def evalZeroOne (n : ℕ) (hn : 1 ≤ n) : B n →+* ℚ :=
  Ideal.Quotient.lift (Ideal.span ({fermatEquation n} : Set Poly)) evalZeroOnePoly
    (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      rw [map_mul, evalZeroOnePoly_fermat n hn, zero_mul])

@[simp] theorem evalZeroOne_coordX (n : ℕ) (hn : 1 ≤ n) : evalZeroOne n hn (coordX n) = 0 := by
  rw [coordX, evalZeroOne, Ideal.Quotient.lift_mk]
  exact evalZeroOnePoly_X0
@[simp] theorem evalZeroOne_coordY (n : ℕ) (hn : 1 ≤ n) : evalZeroOne n hn (coordY n) = 1 := by
  rw [coordY, evalZeroOne, Ideal.Quotient.lift_mk]
  exact evalZeroOnePoly_X1

instance ker_evalZeroOne_isPrime (n : ℕ) (hn : 1 ≤ n) :
    (RingHom.ker (evalZeroOne n hn)).IsPrime :=
  RingHom.ker_isPrime _

abbrev LocalRing0 (n : ℕ) (hn : 1 ≤ n) : Type :=
  Localization.AtPrime (RingHom.ker (evalZeroOne n hn))

noncomputable def cofactorY (n : ℕ) : B n := ∑ i ∈ Finset.range n, coordY n ^ i

theorem one_sub_mul_cofactorY (n : ℕ) :
    (1 - coordY n) * cofactorY n = 1 - coordY n ^ n := by
  rw [cofactorY, mul_comm, geom_sum_mul_neg]

@[simp] theorem evalZeroOne_cofactorY (n : ℕ) (hn : 1 ≤ n) :
    evalZeroOne n hn (cofactorY n) = (n : ℚ) := by
  rw [cofactorY, map_sum]
  simp [evalZeroOne_coordY]

theorem cofactorY_not_mem_ker (n : ℕ) (hn : 1 ≤ n) :
    cofactorY n ∉ RingHom.ker (evalZeroOne n hn) := by
  intro h
  have h0 : evalZeroOne n hn (cofactorY n) = 0 := h
  rw [evalZeroOne_cofactorY n hn] at h0
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  exact hn0 h0

theorem cofactorY_isUnit_localized (n : ℕ) (hn : 1 ≤ n) :
    IsUnit ((algebraMap (B n) (LocalRing0 n hn)) (cofactorY n)) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff (S := LocalRing0 n hn)
    (I := RingHom.ker (evalZeroOne n hn)) (x := cofactorY n)).mpr (cofactorY_not_mem_ker n hn)

/-- At lambda = 0, x^n is a unit times the boundary uniformizer (1 - y) in the local ring
at the rational point (0,1): the algebraic core of ramification index n. -/
theorem boundary_zero_uniformizer_power (n : ℕ) (hn : 1 ≤ n) :
    ∃ u : (LocalRing0 n hn)ˣ,
      algebraMap (B n) (LocalRing0 n hn) (coordX n ^ n) =
        (u : LocalRing0 n hn) * algebraMap (B n) (LocalRing0 n hn) (1 - coordY n) := by
  obtain ⟨u, hu⟩ := cofactorY_isUnit_localized n hn
  refine ⟨u, ?_⟩
  have hfactor : coordX n ^ n = (1 - coordY n) * cofactorY n := by
    rw [lambda_eq_x_pow n, ← one_sub_mul_cofactorY n]
  calc algebraMap (B n) (LocalRing0 n hn) (coordX n ^ n)
      = algebraMap (B n) (LocalRing0 n hn) ((1 - coordY n) * cofactorY n) := by rw [hfactor]
    _ = algebraMap (B n) (LocalRing0 n hn) (1 - coordY n) *
          algebraMap (B n) (LocalRing0 n hn) (cofactorY n) := map_mul _ _ _
    _ = algebraMap (B n) (LocalRing0 n hn) (1 - coordY n) * ↑u := by rw [← hu]
    _ = ↑u * algebraMap (B n) (LocalRing0 n hn) (1 - coordY n) := mul_comm _ _

/-! ## The boundary point lambda = 1, i.e. (x,y) = (1,0) -/

def evalOneZeroPoly : Poly →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun i : Fin 2 => if i = 0 then 1 else 0)

@[simp] theorem evalOneZeroPoly_X0 : evalOneZeroPoly (MvPolynomial.X 0) = 1 := by
  rw [evalOneZeroPoly, MvPolynomial.eval₂Hom_X']
  simp
@[simp] theorem evalOneZeroPoly_X1 : evalOneZeroPoly (MvPolynomial.X 1) = 0 := by
  rw [evalOneZeroPoly, MvPolynomial.eval₂Hom_X']
  simp

theorem evalOneZeroPoly_fermat (n : ℕ) (hn : 1 ≤ n) : evalOneZeroPoly (fermatEquation n) = 0 := by
  rw [fermatEquation, map_sub, map_add, map_pow, map_pow, map_one, evalOneZeroPoly_X0,
    evalOneZeroPoly_X1]
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  simp [zero_pow hn0]

noncomputable def evalOneZero (n : ℕ) (hn : 1 ≤ n) : B n →+* ℚ :=
  Ideal.Quotient.lift (Ideal.span ({fermatEquation n} : Set Poly)) evalOneZeroPoly
    (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      rw [map_mul, evalOneZeroPoly_fermat n hn, zero_mul])

@[simp] theorem evalOneZero_coordX (n : ℕ) (hn : 1 ≤ n) : evalOneZero n hn (coordX n) = 1 := by
  rw [coordX, evalOneZero, Ideal.Quotient.lift_mk]
  exact evalOneZeroPoly_X0
@[simp] theorem evalOneZero_coordY (n : ℕ) (hn : 1 ≤ n) : evalOneZero n hn (coordY n) = 0 := by
  rw [coordY, evalOneZero, Ideal.Quotient.lift_mk]
  exact evalOneZeroPoly_X1

instance ker_evalOneZero_isPrime (n : ℕ) (hn : 1 ≤ n) :
    (RingHom.ker (evalOneZero n hn)).IsPrime :=
  RingHom.ker_isPrime _

abbrev LocalRing1 (n : ℕ) (hn : 1 ≤ n) : Type :=
  Localization.AtPrime (RingHom.ker (evalOneZero n hn))

noncomputable def cofactorX (n : ℕ) : B n := ∑ i ∈ Finset.range n, coordX n ^ i

theorem one_sub_mul_cofactorX (n : ℕ) :
    (1 - coordX n) * cofactorX n = 1 - coordX n ^ n := by
  rw [cofactorX, mul_comm, geom_sum_mul_neg]

@[simp] theorem evalOneZero_cofactorX (n : ℕ) (hn : 1 ≤ n) :
    evalOneZero n hn (cofactorX n) = (n : ℚ) := by
  rw [cofactorX, map_sum]
  simp [evalOneZero_coordX]

theorem cofactorX_not_mem_ker (n : ℕ) (hn : 1 ≤ n) :
    cofactorX n ∉ RingHom.ker (evalOneZero n hn) := by
  intro h
  have h0 : evalOneZero n hn (cofactorX n) = 0 := h
  rw [evalOneZero_cofactorX n hn] at h0
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  exact hn0 h0

theorem cofactorX_isUnit_localized (n : ℕ) (hn : 1 ≤ n) :
    IsUnit ((algebraMap (B n) (LocalRing1 n hn)) (cofactorX n)) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff (S := LocalRing1 n hn)
    (I := RingHom.ker (evalOneZero n hn)) (x := cofactorX n)).mpr (cofactorX_not_mem_ker n hn)

/-- At lambda = 1, y^n is a unit times the boundary uniformizer (1 - x) in the local ring
at the rational point (1,0): the second ramification index n core. -/
theorem boundary_one_uniformizer_power (n : ℕ) (hn : 1 ≤ n) :
    ∃ u : (LocalRing1 n hn)ˣ,
      algebraMap (B n) (LocalRing1 n hn) (coordY n ^ n) =
        (u : LocalRing1 n hn) * algebraMap (B n) (LocalRing1 n hn) (1 - coordX n) := by
  obtain ⟨u, hu⟩ := cofactorX_isUnit_localized n hn
  refine ⟨u, ?_⟩
  have hfactor : coordY n ^ n = (1 - coordX n) * cofactorX n := by
    rw [← one_sub_lambda_eq_y_pow n, ← one_sub_mul_cofactorX n]
  calc algebraMap (B n) (LocalRing1 n hn) (coordY n ^ n)
      = algebraMap (B n) (LocalRing1 n hn) ((1 - coordX n) * cofactorX n) := by rw [hfactor]
    _ = algebraMap (B n) (LocalRing1 n hn) (1 - coordX n) *
          algebraMap (B n) (LocalRing1 n hn) (cofactorX n) := map_mul _ _ _
    _ = algebraMap (B n) (LocalRing1 n hn) (1 - coordX n) * ↑u := by rw [← hu]
    _ = ↑u * algebraMap (B n) (LocalRing1 n hn) (1 - coordX n) := mul_comm _ _

#print axioms boundary_zero_uniformizer_power
#print axioms boundary_one_uniformizer_power
end LeanFormal.IUT.XiFPaper.Mzk1G1OmegaRamificationLocalActual

