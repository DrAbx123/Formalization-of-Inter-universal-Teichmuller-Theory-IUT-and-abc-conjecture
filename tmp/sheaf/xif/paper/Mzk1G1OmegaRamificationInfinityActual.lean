/- G1-B infinity boundary ramification over a general field K with zeta^n = -1:
at the point (s,r) = (zeta,0) of K[s,r]/(1+s^n-r^n), the n-th power of the fibre
coordinate r equals a unit times (s-zeta) in the local ring.  This is the e = n
algebraic core at infinity (route 3.2); taking K = Q(zeta) covers all n. -/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1OmegaRamificationInfinityActual

open MvPolynomial

/-- The infinity chart ring over K: K[s,r]/(1 + s^n - r^n). -/
abbrev InfChart (K : Type) [Field K] (n : Nat) : Type :=
  MvPolynomial (Fin 2) K ⧸ Ideal.span ({1 + MvPolynomial.X 0 ^ n - MvPolynomial.X 1 ^ n} :
    Set (MvPolynomial (Fin 2) K))

/-- The s-coordinate on the infinity chart. -/
def sInf (K : Type) [Field K] (n : Nat) : InfChart K n :=
  Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The r-coordinate on the infinity chart. -/
def rInf (K : Type) [Field K] (n : Nat) : InfChart K n :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

section

variable {K : Type} [Field K] [CharZero K]

/-- Evaluation at (s,r) = (zeta,0) on the polynomial ring. -/
def evalζ0Poly (ζ : K) : MvPolynomial (Fin 2) K →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K) (fun i : Fin 2 => if i = 0 then ζ else 0)

@[simp] theorem evalζ0Poly_X0 (ζ : K) : evalζ0Poly ζ (MvPolynomial.X 0) = ζ := by
  rw [evalζ0Poly, MvPolynomial.eval₂Hom_X']
  simp
@[simp] theorem evalζ0Poly_X1 (ζ : K) : evalζ0Poly ζ (MvPolynomial.X 1) = 0 := by
  rw [evalζ0Poly, MvPolynomial.eval₂Hom_X']
  simp

theorem evalζ0Poly_rel (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) :
    evalζ0Poly ζ (1 + MvPolynomial.X 0 ^ n - MvPolynomial.X 1 ^ n) = 0 := by
  rw [map_sub, map_add, map_one, map_pow, map_pow, evalζ0Poly_X0, evalζ0Poly_X1, hζ]
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  simp [zero_pow hn0]

/-- Evaluation at (zeta,0) on the infinity chart ring. -/
def evalζ0 (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) : InfChart K n →+* K :=
  Ideal.Quotient.lift _ (evalζ0Poly ζ)
    (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      rw [map_mul, evalζ0Poly_rel n hn ζ hζ, zero_mul])

@[simp] theorem evalζ0_s (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) :
    evalζ0 n hn ζ hζ (sInf K n) = ζ := by
  rw [sInf, evalζ0, Ideal.Quotient.lift_mk]
  exact evalζ0Poly_X0 ζ

@[simp] theorem evalζ0_r (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) :
    evalζ0 n hn ζ hζ (rInf K n) = 0 := by
  rw [rInf, evalζ0, Ideal.Quotient.lift_mk]
  exact evalζ0Poly_X1 ζ

theorem evalζ0_algebraMap (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) (c : K) :
    evalζ0 n hn ζ hζ (algebraMap K (InfChart K n) c) = c := by
  rw [show algebraMap K (InfChart K n) c =
      Ideal.Quotient.mk _ (algebraMap K (MvPolynomial (Fin 2) K) c) from rfl]
  rw [MvPolynomial.algebraMap_eq]
  rw [evalζ0, Ideal.Quotient.lift_mk]
  rw [evalζ0Poly]
  exact MvPolynomial.eval₂Hom_C (RingHom.id K) (fun i : Fin 2 => if i = 0 then ζ else 0) c

/-- The relation 1 + s^n = r^n on the infinity chart. -/
theorem relation_inf (n : Nat) : 1 + sInf K n ^ n = rInf K n ^ n := by
  have h : Ideal.Quotient.mk (Ideal.span
      ({1 + MvPolynomial.X 0 ^ n - MvPolynomial.X 1 ^ n} : Set (MvPolynomial (Fin 2) K)))
      (1 + MvPolynomial.X 0 ^ n - MvPolynomial.X 1 ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have h' : 1 + sInf K n ^ n - rInf K n ^ n = 0 := by
    simpa [sInf, rInf, map_add, map_sub, map_pow, map_one] using h
  exact sub_eq_zero.mp h'

/-- The cofactor Q(s) = sum_{i<n} s^i zeta^(n-1-i). -/
def cofInf (K : Type) [Field K] (n : Nat) (ζ : K) : InfChart K n :=
  ∑ i ∈ Finset.range n, sInf K n ^ i * (algebraMap K (InfChart K n) ζ) ^ (n - 1 - i)

theorem cofInf_mul (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) :
    cofInf K n ζ * (sInf K n - algebraMap K (InfChart K n) ζ) = rInf K n ^ n := by
  have hgeom := geom_sum₂_mul_add (sInf K n - algebraMap K (InfChart K n) ζ)
    (algebraMap K (InfChart K n) ζ) n
  simp only [sub_add_cancel] at hgeom
  have hζS : (algebraMap K (InfChart K n) ζ) ^ n = -1 := by
    rw [← map_pow, hζ, map_neg, map_one]
  rw [hζS] at hgeom
  have hQ : cofInf K n ζ * (sInf K n - algebraMap K (InfChart K n) ζ) =
      sInf K n ^ n + 1 := by
    rw [cofInf]
    linear_combination hgeom
  rw [hQ]
  rw [add_comm, relation_inf (K := K) n]

theorem evalζ0_cof (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) :
    evalζ0 n hn ζ hζ (cofInf K n ζ) = (n : K) * ζ ^ (n - 1) := by
  rw [cofInf, map_sum]
  have hterm : ∀ i ∈ Finset.range n,
      evalζ0 n hn ζ hζ (sInf K n ^ i * (algebraMap K (InfChart K n) ζ) ^ (n - 1 - i)) =
        ζ ^ (n - 1) := by
    intro i hi
    rw [map_mul, map_pow, map_pow, evalζ0_s, evalζ0_algebraMap]
    rw [← pow_add]
    congr 1
    have hi' : i < n := Finset.mem_range.mp hi
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem cofInf_eval_ne_zero (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) :
    evalζ0 n hn ζ hζ (cofInf K n ζ) ≠ 0 := by
  rw [evalζ0_cof n hn ζ hζ]
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.one_le_iff_ne_zero.mp hn)] at hζ
    exact (neg_ne_zero.mpr one_ne_zero) hζ.symm
  exact mul_ne_zero hn0 (pow_ne_zero _ hζ0)

instance ker_evalζ0_isPrime (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) :
    (RingHom.ker (evalζ0 n hn ζ hζ)).IsPrime :=
  RingHom.ker_isPrime _

abbrev LocalRingInf (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) : Type :=
  Localization.AtPrime (RingHom.ker (evalζ0 n hn ζ hζ))

theorem cofInf_not_mem_ker (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) :
    cofInf K n ζ ∉ RingHom.ker (evalζ0 n hn ζ hζ) := by
  intro h
  have h0 : evalζ0 n hn ζ hζ (cofInf K n ζ) = 0 := h
  exact cofInf_eval_ne_zero n hn ζ hζ h0

theorem cofInf_isUnit_localized (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) :
    IsUnit ((algebraMap (InfChart K n) (LocalRingInf n hn ζ hζ)) (cofInf K n ζ)) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff (S := LocalRingInf n hn ζ hζ)
    (I := RingHom.ker (evalζ0 n hn ζ hζ)) (x := cofInf K n ζ)).mpr
    (cofInf_not_mem_ker n hn ζ hζ)

/-- At infinity (point (zeta,0)), the fibre coordinate r^n differs from (s - zeta) by a
unit in the local ring: the e = n algebraic core.  Taking K = Q(zeta) covers every n. -/
theorem boundary_infinity_uniformizer_power (n : Nat) (hn : 1 ≤ n) (ζ : K) (hζ : ζ ^ n = -1) :
    ∃ u : (LocalRingInf n hn ζ hζ)ˣ,
      algebraMap (InfChart K n) (LocalRingInf n hn ζ hζ) (rInf K n ^ n) =
        (u : LocalRingInf n hn ζ hζ) *
          algebraMap (InfChart K n) (LocalRingInf n hn ζ hζ)
            (sInf K n - algebraMap K (InfChart K n) ζ) := by
  obtain ⟨u, hu⟩ := cofInf_isUnit_localized n hn ζ hζ
  refine ⟨u, ?_⟩
  calc algebraMap (InfChart K n) (LocalRingInf n hn ζ hζ) (rInf K n ^ n)
      = algebraMap (InfChart K n) (LocalRingInf n hn ζ hζ)
          (cofInf K n ζ * (sInf K n - algebraMap K (InfChart K n) ζ)) := by
          rw [cofInf_mul n hn ζ hζ]
    _ = algebraMap (InfChart K n) (LocalRingInf n hn ζ hζ) (cofInf K n ζ) *
          algebraMap (InfChart K n) (LocalRingInf n hn ζ hζ)
            (sInf K n - algebraMap K (InfChart K n) ζ) := map_mul _ _ _
    _ = (u : LocalRingInf n hn ζ hζ) *
          algebraMap (InfChart K n) (LocalRingInf n hn ζ hζ)
            (sInf K n - algebraMap K (InfChart K n) ζ) := by rw [hu]

end

#print axioms boundary_infinity_uniformizer_power
end LeanFormal.IUT.XiFPaper.Mzk1G1OmegaRamificationInfinityActual
