import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.IUTIV.Estimates.DifferentDegreeUpperBound

/-!
# The different upper bound on actual finite extensions of Qp

This specializes IUT IV Proposition 1.3(ii) to the existing norm-integer
rings and `localDifferentPaperOrder`. The integer extension, its finiteness,
and the valuation/degree identifications are constructed in the proof.
-/

namespace LeanFormal.IUT.LocalDifferentUpperBound

open IsLocalRing UniqueFactorizationMonoid
open LeanFormal.IUT.LocalFieldIntegralUnits LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.IntegralTraceDualTensorInclusion LeanFormal.IUT.IUTIV.Estimates

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

private theorem generator_addVal_toNat_eq_factorCount
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ideal : Ideal R) (nonzero : ideal ≠ ⊥) :
    (IsDiscreteValuationRing.addVal R (Submodule.IsPrincipal.generator ideal)).toNat =
      (normalizedFactors ideal).count (maximalIdeal R) := by
  have equality := congrArg (IsDiscreteValuationRing.idealOrderIsoENat R)
    (dvr_ideal_eq_pow_factorCount R ideal nonzero)
  rw [← IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe,
    OrderIso.apply_symm_apply] at equality
  change IsDiscreteValuationRing.addVal R (Submodule.IsPrincipal.generator ideal) =
    ((normalizedFactors ideal).count (maximalIdeal R) : ℕ∞) at equality
  simpa using congrArg ENat.toNat equality

private theorem span_factorCount_eq_addVal_toNat
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (element : R) (nonzero : element ≠ 0) :
    (normalizedFactors (Ideal.span {element})).count (maximalIdeal R) =
      (IsDiscreteValuationRing.addVal R element).toNat := by
  rw [← generator_addVal_toNat_eq_factorCount R _ (by simpa using nonzero)]
  congr 1
  exact (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr
    (Submodule.IsPrincipal.associated_generator_span_self element)

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

theorem localDifferentOrder_eq_factorCount [IsDiscreteValuationRing (Integers K)] :
    localDifferentOrder (p := p) (L := K) =
      (normalizedFactors (differentIdeal ℤ_[p] (Integers K))).count
        (maximalIdeal (Integers K)) := by
  letI : IsDiscreteValuationRing (Integers K) := integersIsDiscreteValuationRing (p := p)
  letI : IsDedekindDomain (Integers K) := integersIsDedekindDomain (p := p)
  exact generator_addVal_toNat_eq_factorCount (Integers K)
    (differentIdeal ℤ_[p] (Integers K)) differentIdeal_ne_bot

theorem logShellRamificationExponent_eq_ramificationIdx :
    logShellRamificationExponent (K := K) (p := p) =
      (maximalIdeal ℤ_[p]).ramificationIdx' (maximalIdeal (Integers K)) := by
  letI : IsDiscreteValuationRing (Integers K) := integersIsDiscreteValuationRing (p := p)
  letI : IsDedekindDomain (Integers K) := integersIsDedekindDomain (p := p)
  have mapped_prime : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (Integers K)) =
      Ideal.span {(p : Integers K)} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span]
    simp
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
    (Ideal.map_ne_bot_of_ne_bot (S := Integers K) (dvr_maximalIdeal_ne_bot ℤ_[p]))
    (inferInstance : (maximalIdeal (Integers K)).IsPrime)
    (dvr_maximalIdeal_ne_bot (Integers K)), mapped_prime,
    span_factorCount_eq_addVal_toNat (Integers K) _
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]
  have prime_order : IsDiscreteValuationRing.addVal (Integers K) (p : Integers K) =
      (logShellRamificationExponent (K := K) (p := p) : ℕ∞) := by
    simpa [ramifiedPrimeAddVal] using addVal_prime_eq_ramificationExponent (K := K) (p := p)
  rw [prime_order]
  simp

variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
  [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L] [NormedAlgebra K L] [IsScalarTower ℚ_[p] K L]

/-- The field inclusion maps actual norm-integers to norm-integers. -/
noncomputable def integersExtensionMap : Integers K →+* Integers L :=
  RingHom.codRestrict ((algebraMap K L).comp (Integers K).subtype) (Integers L)
    (fun element ↦ by
      change ‖algebraMap K L (element : K)‖ ≤ 1
      rw [norm_algebraMap']
      exact element.property)

@[implicit_reducible] noncomputable def integersExtensionAlgebra :
    Algebra (Integers K) (Integers L) :=
  (integersExtensionMap (K := K) (L := L)).toAlgebra

@[implicit_reducible] noncomputable def integersToExtensionFieldAlgebra : Algebra (Integers K) L :=
  Algebra.restrictScalars (Integers K) K L

attribute [local instance 50] integersExtensionAlgebra integersToExtensionFieldAlgebra

local instance integersExtensionFieldTower : IsScalarTower (Integers K) K L :=
  IsScalarTower.of_algebraMap_eq (R := Integers K) (S := K) (A := L) fun _ ↦ rfl

local instance integersExtensionInclusionTower : IsScalarTower (Integers K) (Integers L) L :=
  IsScalarTower.of_algebraMap_eq (R := Integers K) (S := Integers L) (A := L) fun _ ↦ rfl

local instance integersExtensionZpTower : IsScalarTower ℤ_[p] (Integers K) (Integers L) :=
  IsScalarTower.of_algebraMap_eq (R := ℤ_[p]) (S := Integers K) (A := Integers L) fun scalar ↦ by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply ℚ_[p] K L (scalar : ℚ_[p])

include p in
omit [CharZero K] [CompleteSpace K] [ProperSpace K] [FiniteDimensional ℚ_[p] K]
    [CharZero L] [CompleteSpace L] in
private theorem integersExtensionFinite : Module.Finite (Integers K) (Integers L) :=
  Module.Finite.of_restrictScalars_finite ℤ_[p] (Integers K) (Integers L)

local instance integersExtensionTorsionFree : Module.IsTorsionFree (Integers K) (Integers L) :=
  Module.IsTorsionFree.of_smul_eq_zero fun scalar element equality ↦ by
    have product_zero : algebraMap K L (scalar : K) * (element : L) = 0 :=
      congrArg (fun integer : Integers L ↦ (integer : L)) equality
    rcases mul_eq_zero.mp product_zero with scalar_zero | element_zero
    · exact Or.inl (Subtype.ext ((algebraMap K L).injective (by simpa using scalar_zero)))
    · exact Or.inr (Subtype.ext element_zero)

omit [CharZero K] [CompleteSpace K] [ProperSpace K]
    [CharZero L] [CompleteSpace L] [ProperSpace L] in
theorem fractionRing_integer_degree_eq :
    Module.finrank (FractionRing (Integers K)) (FractionRing (Integers L)) =
      Module.finrank K L := by
  apply Algebra.finrank_eq_of_equiv_equiv
    (FractionRing.algEquiv (Integers K) K).toRingEquiv
    (FractionRing.algEquiv (Integers L) L).toRingEquiv
  ext element
  exact IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv (Integers K) K) (FractionRing.algEquiv (Integers L) L) element

/-- IUT IV Proposition 1.3(ii), expressed using the repository's actual
local different orders, ramification exponents, and the field degree `[L:K]`. -/
theorem localDifferentPaperOrder_le_degree_padicVal :
    localDifferentPaperOrder (p := p) (L := L) ≤
      localDifferentPaperOrder (p := p) (L := K) +
        padicValNat p (Module.finrank K L) +
        1 / (logShellRamificationExponent (K := K) (p := p) : ℝ) := by
  letI : IsDiscreteValuationRing (Integers K) := integersIsDiscreteValuationRing (p := p)
  letI : IsDiscreteValuationRing (Integers L) := integersIsDiscreteValuationRing (p := p)
  letI : IsDedekindDomain (Integers K) := integersIsDedekindDomain (p := p)
  letI : IsDedekindDomain (Integers L) := integersIsDedekindDomain (p := p)
  letI : Module.Finite (Integers K) (Integers L) := integersExtensionFinite (p := p)
  letI : (maximalIdeal (Integers K)).LiesOver (maximalIdeal ℤ_[p]) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap ℤ_[p] (Integers K))).symm⟩
  letI : (maximalIdeal (Integers L)).LiesOver (maximalIdeal (Integers K)) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap (Integers K) (Integers L))).symm⟩
  letI : IsIntegralClosure (Integers L) ℤ_[p] (FractionRing (Integers L)) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  letI : IsLocalization (Algebra.algebraMapSubmonoid (Integers L) (nonZeroDivisors ℤ_[p]))
      (FractionRing (Integers L)) :=
    IsIntegralClosure.isLocalization ℤ_[p] (FractionRing ℤ_[p])
      (FractionRing (Integers L)) (Integers L)
  letI : FiniteDimensional (FractionRing ℤ_[p]) (FractionRing (Integers L)) :=
    .of_isLocalization ℤ_[p] (Integers L) (nonZeroDivisors ℤ_[p])
  have estimate := iutIVProp13ii_normalizedDifferent_le ℤ_[p] (Integers K) (Integers L) p
    PadicInt.maximalIdeal_eq_span_p.symm
  rw [fractionRing_integer_degree_eq (K := K) (L := L),
    ← logShellRamificationExponent_eq_ramificationIdx (K := K) (p := p),
    ← logShellRamificationExponent_eq_ramificationIdx (K := L) (p := p),
    ← localDifferentOrder_eq_factorCount (K := K) (p := p),
    ← localDifferentOrder_eq_factorCount (K := L) (p := p)] at estimate
  exact estimate

end LeanFormal.IUT.LocalDifferentUpperBound
