import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceHolomorphicIntegerIndex
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Base case for the holomorphic different/discriminant comparison

This file proves the self-extension base case needed by
`ArithmeticTupleHolomorphicDifferentInterface`.  For a Dedekind domain `A`, the
trace form of the self-extension `FractionRing A / A` is the multiplication
form, so the integral trace dual of the unit submodule is contained in the unit
submodule.  Consequently `differentIdeal A A` is the unit ideal.

Specializing to `A = Z_p` gives

`differentIdeal Z_p Z_p = top` and `cardQuot (differentIdeal Z_p Z_p) = 1`.

For a finite family with every integral model equal to `Z_p`, the product of
local different quotient cardinalities is therefore one.  The final
conditional theorem feeds that calculation into the existing holomorphic
different interface.  It does not prove the interface itself, and it does not
identify general Smith-normal-form exponents with local different exponents.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open Submodule

noncomputable section

universe u v w

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

/-! ## The trace dual of the unit submodule in a self-extension -/

/-- In the self-extension `K / A`, the trace of `x * 1` is `x`.  Therefore the
trace dual of the unit submodule is contained in the unit submodule. -/
theorem traceDual_one_le_one_self
    {A K : Type*} [CommRing A] [Field K] [Algebra A K] :
    Submodule.traceDual A K (1 : Submodule A K) ≤ 1 := by
  intro x hx
  rw [Submodule.mem_one]
  have hx' :=
    (Submodule.mem_traceDual (A := A) (K := K) (L := K) (B := A)
      (I := (1 : Submodule A K))).mp hx 1
      (Submodule.mem_one.mpr ⟨1, map_one (algebraMap A K)⟩)
  rw [Algebra.traceForm_apply, mul_one, Algebra.trace_self_apply] at hx'
  exact hx'

/-- The different ideal of a Dedekind domain over itself is the unit ideal.

This is the self-extension `FractionRing A / A`.  The unit element lies in the
inverse of the integral trace dual because that dual is contained in the unit
submodule. -/
theorem differentIdeal_self_eq_top
    (A : Type*) [CommRing A] [IsDedekindDomain A] :
    differentIdeal A A = ⊤ := by
  rw [Ideal.eq_top_iff_one, differentIdeal, Submodule.mem_comap]
  change algebraMap A (FractionRing A) 1 ∈
    (1 : Submodule A (FractionRing A)) /
      Submodule.traceDual A (FractionRing A) 1
  rw [map_one, Submodule.one_mem_div]
  exact traceDual_one_le_one_self (A := A) (K := FractionRing A)

/-! ## The base case at the p-adic integers -/

/-- The different ideal of `Z_p` over itself is the unit ideal. -/
theorem differentIdeal_padicInt_self_eq_top (p : ℕ) [Fact p.Prime] :
    differentIdeal ℤ_[p] ℤ_[p] = ⊤ :=
  differentIdeal_self_eq_top ℤ_[p]

/-- The quotient by the self-different of `Z_p` has cardinality one. -/
theorem cardQuot_differentIdeal_padicInt_self_eq_one (p : ℕ) [Fact p.Prime] :
    Submodule.cardQuot (differentIdeal ℤ_[p] ℤ_[p]) = 1 := by
  rw [differentIdeal_padicInt_self_eq_top p, Submodule.cardQuot_top]

/-- In a finite family whose every integral model is `Z_p`, the different
quotient product appearing in the holomorphic interface is one. -/
theorem prod_cardQuot_differentIdeal_padicInt_self_eq_one
    (p : ℕ) [Fact p.Prime] {J : Type*} [Fintype J] :
    (∏ j : J,
      Submodule.cardQuot
        (differentIdeal ℤ_[p] ((fun _ : J => ℤ_[p]) j))) = 1 := by
  apply Finset.prod_eq_one
  intro j _
  exact cardQuot_differentIdeal_padicInt_self_eq_one p

/-! ## Interface specialization -/

/-- If the existing holomorphic different interface holds for a rank-one
diagonal model `E = J -> Q_p`, then the product side is computed by the
self-different base case, so the actual holomorphic index is one.

The hypothesis `h` is the still-unproved general comparison.  This theorem
performs the base-case substitution; it does not claim that `h` holds. -/
theorem arithmeticTupleIntegerTensorHolomorphicIndex_eq_one_of_differentInterface_rankOne
    {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, Fintype (V i)]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i)
    {J : Type} [Fintype J]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((_ : J) → ℚ_[p]))
    (h : ArithmeticTupleHolomorphicDifferentInterface places tuple J
      (fun _ : J => ℚ_[p]) e) :
    arithmeticTupleIntegerTensorHolomorphicIndex places tuple = 1 := by
  calc
    arithmeticTupleIntegerTensorHolomorphicIndex places tuple =
        ∏ j : J,
          Submodule.cardQuot
            (differentIdeal ℤ_[p] ((fun _ : J => ℤ_[p]) j)) :=
      h (fun _ : J => ℤ_[p])
    _ = 1 := prod_cardQuot_differentIdeal_padicInt_self_eq_one p

end

end LeanFormal.IUT.NumberFieldFinitePlace
