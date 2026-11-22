import tmp.sheaf.xif.paper.S2141D5FactorizationFieldsActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2126Mod29IntegrationActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
import tmp.sheaf.xif.paper.S2454D5FinalIntegrationActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2492Mod29FactorizationActual
open LeanFormal.IUT.XiFPaper.S2141D5FactorizationFieldsActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
lemma S2492_four_ne_zero : (4 : ZMod 29) ≠ 0 := by
  intro h
  have hdiv : (29 : ℕ) ∣ 4 := (ZMod.natCast_eq_zero_iff 4 29).mp h
  norm_num at hdiv
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
/-! ## 2. The actual mod-29 factorization and its factor degrees -/

/-- The monic quadratic factor `x^2 + 6x + 12` of the corrected mod-29
product, written in expanded form for the finite computation. -/
def S2491Factor2Expanded : (ZMod 29)[X] :=
  C (12 : ZMod 29) + C 6 * X + X ^ 2

/-- The expanded quadratic is the S2132 quadratic factor. -/
theorem S2491Factor2Expanded_eq :
    S2491Factor2Expanded = S2141Factor2 := by
  rfl

/-- The quadratic factor is irreducible over `F_29`: its discriminant
`36 - 48 = 17` is a non-square, checked by the finite root computation. -/
theorem S2491Factor2Expanded_irreducible :
    Irreducible S2491Factor2Expanded := by
  have hdeg : S2491Factor2Expanded.natDegree = 2 := by
    unfold S2491Factor2Expanded
    compute_degree!
  refine irreducible_of_degree_le_three_of_not_isRoot (K := ZMod 29) ?_ ?_
  · rw [hdeg]
    norm_num
  · intro x hx
    have hnot : ∀ y : ZMod 29,
        (12 : ZMod 29) + 6 * y + y ^ 2 ≠ 0 := by
      decide +revert
    exact hnot x (by simpa [S2491Factor2Expanded, IsRoot] using hx)

/-- The S2141 quadratic factor is irreducible. -/
theorem S2491Factor2_irreducible : Irreducible S2141Factor2 := by
  rw [← S2491Factor2Expanded_eq]
  exact S2491Factor2Expanded_irreducible

/-- The un-scaled expanded degree-ten factor
`x^10 + 7x^7 + 5x^6 + 8x^5 - 5x^4 + 14x^3 - 13x^2 - 5x + 10`. -/
def S2491F10Base : (ZMod 29)[X] :=
  C 10 - C 5 * X - C 13 * X ^ 2 + C 14 * X ^ 3 - C 5 * X ^ 4 +
    C 8 * X ^ 5 + C 5 * X ^ 6 + C 7 * X ^ 7 - C 4 * X ^ 9 + X ^ 10

/-- The S2141 degree-ten factor is the unit multiple `4 * S2491F10Base`. -/
theorem S2491Factor10_eq_scaled :
    S2141Factor10 = C (4 : ZMod 29) * S2491F10Base :=
  rfl

/-- The un-scaled degree-ten factor is exactly the S2126 polynomial `f` of
S2132. -/
theorem S2491F10Base_eq : S2491F10Base = S2132Factor10 := by
  ext n
  by_cases hn : n ≤ 10
  · interval_cases n <;>
      (simp [S2491F10Base, S2132Factor10, _root_.f, coeff_add, coeff_sub,
        coeff_mul, coeff_C, coeff_X_pow, coeff_X, coeff_monomial] <;>
        reduce_mod_char <;> decide)
  · have h1 : S2491F10Base.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      unfold S2491F10Base
      compute_degree!
      omega
    have h2 : S2132Factor10.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [S2132Factor10_eq_s2126, _root_.hfdeg]
      omega
    rw [h1, h2]

/-- The un-scaled degree-ten factor is monic. -/
theorem S2491F10Base_monic : S2491F10Base.Monic := by
  rw [S2491F10Base_eq, S2132Factor10_eq_s2126]
  exact _root_.hfmonic

/-- The un-scaled degree-ten factor is irreducible: S2126 proves the
irreducibility of `f`, and `S2491F10Base = f`. -/
theorem S2491F10Base_irreducible : Irreducible S2491F10Base := by
  rw [S2491F10Base_eq]
  exact S2132Factor10_irreducible

/-- The S2141 degree-ten factor is irreducible: it is the unit multiple
`4 * f` of the irreducible S2126 polynomial. -/
theorem S2491Factor10_irreducible : Irreducible S2141Factor10 := by
  have h4 : IsUnit (4 : ZMod 29) :=
    isUnit_iff_ne_zero.mpr S2492_four_ne_zero
  have hu : IsUnit (C (4 : ZMod 29)) := isUnit_C.mpr h4
  have hassoc :
      Associated (C (4 : ZMod 29) * S2491F10Base) S2491F10Base :=
    associated_unit_mul_left S2491F10Base (C (4 : ZMod 29)) hu
  rw [S2491Factor10_eq_scaled]
  exact hassoc.symm.irreducible S2491F10Base_irreducible

/-- The quadratic factor is monic. -/
theorem S2491Factor2_monic : S2141Factor2.Monic := by
  unfold S2141Factor2 S2132Factor2
  monicity!

/-- The actual corrected mod-29 product, re-exported from S2141. -/
theorem S2491Mod29Product :
    S2141Factor2 * S2141Factor10 =
      S2132Psi5Z.map (Int.castRingHom (ZMod 29)) :=
  S2141Product

/-- The exact factor-degree computation: the reduction of the actual integral
model has one irreducible quadratic factor and one irreducible degree-ten
factor, so its factor-degree multiset is `{2, 10}`. -/
theorem S2491FactorDegrees :
    factorDegrees (S2132Psi5Z.map (Int.castRingHom (ZMod 29))) =
      ({2, 10} : Multiset ℕ) := by
  classical
  letI : DecidableEq (ZMod 29) := Classical.decEq _
  rw [← S2141Product]
  unfold factorDegrees
  change (UniqueFactorizationMonoid.normalizedFactors
      (S2141Factor2 * S2141Factor10)).map Polynomial.natDegree =
    ({2, 10} : Multiset ℕ)
  rw [UniqueFactorizationMonoid.normalizedFactors_mul
    S2491Factor2_irreducible.ne_zero S2491Factor10_irreducible.ne_zero]
  have h2norm : UniqueFactorizationMonoid.normalizedFactors S2141Factor2 =
      ({S2141Factor2} : Multiset ((ZMod 29)[X])) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible
      S2491Factor2_irreducible, Monic.normalize_eq_self S2491Factor2_monic]
  have h10norm : UniqueFactorizationMonoid.normalizedFactors S2141Factor10 =
      ({S2132Factor10} : Multiset ((ZMod 29)[X])) := by
    rw [S2491Factor10_eq_scaled]
    rw [UniqueFactorizationMonoid.normalizedFactors_mul
      (Polynomial.C_ne_zero.mpr S2492_four_ne_zero)
      S2491F10Base_irreducible.ne_zero]
    rw [UniqueFactorizationMonoid.normalizedFactors_of_isUnit
      (isUnit_C.mpr (by have h4 : IsUnit (4 : ZMod 29) := isUnit_iff_ne_zero.mpr S2492_four_ne_zero; exact h4))]
    rw [Multiset.zero_add]
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible
      S2491F10Base_irreducible, Monic.normalize_eq_self S2491F10Base_monic,
      S2491F10Base_eq]
  rw [h2norm, h10norm]
  simp only [Multiset.map_add, Multiset.map_singleton]
  rw [S2141Factor2_natDegree, S2132Factor10_eq_s2126, _root_.hfdeg]
  decide

/-- The full concrete mod-29 factorization certificate: product,
irreducibility of both factors, and the factor-degree multiset. -/
theorem S2491ConcreteMod29Factorization :
    S2141Factor2 * S2141Factor10 =
        S2132Psi5Z.map (Int.castRingHom (ZMod 29)) ∧
      Irreducible S2141Factor2 ∧
      Irreducible S2141Factor10 ∧
      factorDegrees (S2132Psi5Z.map (Int.castRingHom (ZMod 29))) =
        ({2, 10} : Multiset ℕ) :=
  ⟨S2141Product, S2491Factor2_irreducible, S2491Factor10_irreducible,
    S2491FactorDegrees⟩

#print axioms S2491Factor2_irreducible
#print axioms S2491Factor10_irreducible
#print axioms S2491FactorDegrees
#print axioms S2491ConcreteMod29Factorization

end LeanFormal.IUT.XiFPaper.S2492Mod29FactorizationActual
end
