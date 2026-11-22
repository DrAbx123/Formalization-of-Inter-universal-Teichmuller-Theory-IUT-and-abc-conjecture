import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeNormalizedCompletion
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Tactic

/-!
# finrank one at a rational common prime

The rational finite-place completion is one-dimensional over its p-adic scalar
field.  The algebra map is bijective: its image is a closed subfield containing
the dense rationals, hence everything.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

open NumberField

/-- The primality of five as a fact instance, for the Q_5 notation. -/
instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The actual Qp-algebra structure on the completion, exposed for the completion
type itself (the library instance is stated for the definitional alias
NormalizedCompletion). -/
instance padicCompletionAlgebraOnCompletion (P : NumberField.FinitePlace ℚ) :
    Algebra (PadicScalarField P) (Completion P) := padicCompletionAlgebra P

section RationalFinrank

variable (P : NumberField.FinitePlace ℚ)

/-- The adic-completion rational algebra structure, made local so that type
class inference uses it for the completion itself. -/
local instance instAlgebraRatCompletionAux : Algebra ℚ (Completion P) :=
  @IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (NumberField.RingOfIntegers ℚ) _ _ ℚ ℚ _ _ _ _ P.maximalIdeal (Algebra.id ℚ)

/-- The rational finite-place completion is one-dimensional over its p-adic
scalar field. -/
theorem finrank_completion_rat :
    Module.finrank (PadicScalarField P) (Completion P) = 1 := by
  haveI hsmul : ContinuousSMul (PadicScalarField P) (Completion P) :=
    continuousSMul_padicCompletionAlgebra P
  have hdense : DenseRange (fun q : ℚ => (q : Completion P)) := by
    have h := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := ℚ) P.maximalIdeal
    have hfun : (fun q : ℚ => (q : Completion P)) =
        ⇑(algebraMap ℚ (Completion P)) := by
      funext q
      exact (map_ratCast (algebraMap ℚ (Completion P)) q).symm
    rw [hfun]
    exact h
  have hrat : Set.range (fun q : ℚ => (q : Completion P)) ⊆
      (Submodule.span (PadicScalarField P) {(1 : Completion P)} : Set (Completion P)) := by
    rw [Set.range_subset_iff]
    intro q
    have hq : (q : Completion P) = algebraMap (PadicScalarField P) (Completion P)
        (algebraMap ℚ (PadicScalarField P) q) := by
      rw [show algebraMap ℚ (PadicScalarField P) q = (q : PadicScalarField P) from rfl]
      exact (map_ratCast (algebraMap (PadicScalarField P) (Completion P)) q).symm
    rw [hq, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton 1))
  have hclosed : IsClosed
      ((Submodule.span (PadicScalarField P) {(1 : Completion P)}) : Set (Completion P)) := by
    haveI : FiniteDimensional (PadicScalarField P)
        ↥(Submodule.span (PadicScalarField P) {(1 : Completion P)}) :=
      FiniteDimensional.span_of_finite (PadicScalarField P) (Set.finite_singleton 1)
    exact Submodule.closed_of_finiteDimensional _
  have htop : Submodule.span (PadicScalarField P) {(1 : Completion P)} = ⊤ := by
    have huniv : (Set.univ : Set (Completion P)) ⊆
        (Submodule.span (PadicScalarField P) {(1 : Completion P)} : Set (Completion P)) := by
      rw [← hdense.closure_eq]
      have h := closure_mono hrat
      rwa [hclosed.closure_eq] at h
    exact SetLike.coe_injective (Set.eq_univ_of_univ_subset huniv)
  have hsurj : Function.Surjective
      (algebraMap (PadicScalarField P) (Completion P)) := by
    intro y
    have hy : y ∈ Submodule.span (PadicScalarField P) {(1 : Completion P)} := by
      rw [htop]
      exact Submodule.mem_top
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨a, ha⟩ := hy
    exact ⟨a, by rw [← ha, Algebra.smul_def, mul_one]⟩
  have hinj : Function.Injective
      (algebraMap (PadicScalarField P) (Completion P)) := by
    intro x y hxy
    have hzero : algebraMap (PadicScalarField P) (Completion P) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    by_contra hne
    have hne0 : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h1 : algebraMap (PadicScalarField P) (Completion P)
        ((x - y) * (x - y)⁻¹) = 1 := by
      rw [mul_inv_cancel₀ hne0, map_one]
    rw [map_mul, hzero, zero_mul] at h1
    exact zero_ne_one h1
  exact Module.finrank_of_bijective_algebraMap ⟨hinj, hsurj⟩

/-- The normalized rational completion is one-dimensional over its p-adic scalar
field. -/
theorem finrank_normalizedCompletion_rat :
    Module.finrank (PadicScalarField P) (NormalizedCompletion P) = 1 :=
  finrank_completion_rat P

end RationalFinrank

/-- The common-prime completion at a rational place above 5 is one-dimensional
over Q_5. -/
theorem finrank_commonPrimeCompletion_rat_of_prime (p : ℕ) [Fact p.Prime]
    (place : FinitePlaceAtPrime ℚ p) :
    Module.finrank ℚ_[p] (CommonPrimeCompletion place) = 1 := by
  rcases place with ⟨P, hp⟩
  cases hp
  exact finrank_normalizedCompletion_rat P

/-- The common-prime completion at a rational place above 5 is one-dimensional
over Q_5. -/
theorem finrank_commonPrimeCompletion_rat (place : FinitePlaceAtPrime ℚ 5) :
    Module.finrank ℚ_[5] (CommonPrimeCompletion place) = 1 :=
  finrank_commonPrimeCompletion_rat_of_prime 5 place

end

end LeanFormal.IUT.NumberFieldFinitePlace