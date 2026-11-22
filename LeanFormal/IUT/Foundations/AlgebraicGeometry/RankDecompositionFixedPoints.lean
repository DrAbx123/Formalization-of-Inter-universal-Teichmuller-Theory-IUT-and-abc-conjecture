import LeanFormal.IUT.Foundations.AlgebraicGeometry.M2FixedPointProduct
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FixedLocalizationAction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.ConstantRankFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPoints
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

/-!
# Rank decomposition and fixed points

Finite projective A/R has locally constant rank at primes, hence a finite
clopen partition of Spec R and idempotent components.  On the constant-rank
component at n, the localized algebra has rank n and its fixed algebra is the
localization of A^G.  For a finite product decomposition, fixed points are the
product of component fixed points (consuming production M2 product).
-/

open AlgebraicGeometry CategoryTheory
open Module

noncomputable section

namespace RankDecompositionFixedPoints

universe u

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Module.Finite R A] [Module.Projective R A]

/-- For a finite projective module, the rank-at-stalk function has finite
range (locally constant on compact Spec R). -/
lemma rankAtStalk_finite_range {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    (Set.range (Module.rankAtStalk (R := R) M)).Finite := by
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  haveI : Module.Flat R M := Module.Flat.of_projective
  have hloc : IsLocallyConstant (Module.rankAtStalk (R := R) M) :=
    Module.isLocallyConstant_rankAtStalk
  exact IsCompact.finite_of_discrete (isCompact_range hloc.continuous)

/-- The rank fibre at n is clopen. -/
lemma rankFiber_isClopen {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    IsClopen {p : PrimeSpectrum R | Module.rankAtStalk (R := R) M p = n} := by
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  haveI : Module.Flat R M := Module.Flat.of_projective
  exact (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)).isClopen_fiber n

/-- The idempotent defining the rank-n clopen component. -/
noncomputable def rankComponentIdempotent (n : ℕ) : R :=
  (PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
    (rankFiber_isClopen (R := R) (M := A) n)).choose

lemma rankComponentIdempotent_isIdempotent (n : ℕ) :
    IsIdempotentElem (rankComponentIdempotent (R := R) (A := A) n) :=
  (PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
    (rankFiber_isClopen (R := R) (M := A) n)).choose_spec.1.1

lemma rankComponent_basicOpen (n : ℕ) :
    (PrimeSpectrum.basicOpen (rankComponentIdempotent (R := R) (A := A) n) :
        Set (PrimeSpectrum R)) =
      {p : PrimeSpectrum R | Module.rankAtStalk (R := R) A p = n} :=
  (PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
    (rankFiber_isClopen (R := R) (M := A) n)).choose_spec.1.2.symm

/-- On the rank-n idempotent localization, the base-changed algebra has constant
rank n. -/
theorem rankAtStalk_baseChange_component (n : ℕ)
    (p : PrimeSpectrum (Localization.Away (rankComponentIdempotent (R := R) (A := A) n))) :
    Module.rankAtStalk (R := Localization.Away (rankComponentIdempotent (R := R) (A := A) n))
      (TensorProduct R (Localization.Away (rankComponentIdempotent (R := R) (A := A) n)) A) p = n := by
  haveI : Module.Flat R A := Module.Flat.of_projective
  have hmem : PrimeSpectrum.comap (algebraMap R
      (Localization.Away (rankComponentIdempotent (R := R) (A := A) n))) p ∈
      PrimeSpectrum.basicOpen (rankComponentIdempotent (R := R) (A := A) n) := by
    rw [PrimeSpectrum.mem_basicOpen]
    intro hmem
    have hunit : IsUnit (algebraMap R
        (Localization.Away (rankComponentIdempotent (R := R) (A := A) n))
        (rankComponentIdempotent (R := R) (A := A) n)) :=
      IsLocalization.Away.algebraMap_isUnit (rankComponentIdempotent (R := R) (A := A) n)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal hmem hunit)
  rw [Module.rankAtStalk_baseChange]
  exact (Set.ext_iff.mp (rankComponent_basicOpen (R := R) (A := A) n)
    (PrimeSpectrum.comap _ p)).mp hmem

/-- The embedded idempotent in the fixed subalgebra. -/
noncomputable def rankComponentFixedIdempotent (n : ℕ) :
    FixedPoints.subalgebra R A G :=
  ⟨algebraMap R A (rankComponentIdempotent (R := R) (A := A) n), by
    intro g
    exact smul_algebraMap (R := R) (A := A) g (rankComponentIdempotent (R := R) (A := A) n)⟩

/-- Fixed points of a finite G-equivariant product are the product of the
component fixed points (consumer of production M2FixedPointProduct). -/
noncomputable def fixedPointProductAlgEquiv
    {κ : Type*} [Fintype κ] (T : κ → Type u) [∀ k, CommRing (T k)]
    [∀ k, Algebra R (T k)] [∀ k, MulSemiringAction G (T k)]
    [∀ k, SMulCommClass G R (T k)]
    (e : A ≃ₐ[R] (∀ k, T k))
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a) :
    FixedPoints.subalgebra R A G ≃ₐ[R]
      ∀ k, FixedPoints.subalgebra R (T k) G :=
  ABCBridge.M2FixedPointProduct.fixedPointProductAlgEquiv
    (S := R) (B := A) (G := G) T e he

/-- If all constant-rank component fixed algebras are finite etale over R, then
so is the fixed algebra of A. -/
theorem fixedPointSubalgebra_finiteEtale_of_product
    {κ : Type*} [Fintype κ] (T : κ → Type u) [∀ k, CommRing (T k)]
    [∀ k, Algebra R (T k)] [∀ k, MulSemiringAction G (T k)]
    [∀ k, SMulCommClass G R (T k)]
    (e : A ≃ₐ[R] (∀ k, T k))
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    [∀ k, Algebra.Etale R (FixedPoints.subalgebra R (T k) G)]
    [∀ k, Module.Finite R (FixedPoints.subalgebra R (T k) G)] :
    Algebra.Etale R (FixedPoints.subalgebra R A G) ∧
      Module.Finite R (FixedPoints.subalgebra R A G) := by
  let hfix := fixedPointProductAlgEquiv (R := R) (A := A) (G := G) T e he
  exact ⟨Algebra.Etale.of_equiv hfix.symm,
    Module.Finite.equiv hfix.symm.toLinearEquiv⟩

end RankDecompositionFixedPoints
