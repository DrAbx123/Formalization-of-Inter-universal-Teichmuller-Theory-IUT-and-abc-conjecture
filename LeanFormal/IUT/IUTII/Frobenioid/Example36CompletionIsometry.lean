import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionEmbeddingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.Audit.Status
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Foundation F6b: log-norm isometry of the actual completion embedding into PadicAlgCl

This module continues Example36CompletionEmbeddingActual.  The actual completion
K_v = NormalizedCompletion place = Completion place = (place.maximalIdeal).adicCompletion F
(the tree's completion type, with the normalized spectral norm of
FinitePlaceNormalizedCompletion) admits an unconditional injective Q_p-algebra
embedding into PadicAlgCl by the universal property.

## What is actually proved here

* minpoly invariance under a Q_p-algebra homomorphism between Q_p-algebras in
  which the source is algebraic (minpoly_algHom_eq);
* spectral-norm invariance (spectralNorm_algHom_eq), using the tree's/Mathlib's
  identification of the normalized completion norm and the PadicAlgCl norm with
  the spectral norms (both by rfl);
* the resulting **isometry of the actual embedding**
  ||phi x|| = ||x|| for every x in the actual completion, and hence
  Real.log ||phi x|| = Real.log ||x|| for units;
* the exact reduction of the image-side log-norm identity to the normalized
  norm/valuation formula Real.log ||x|| = -(completionValuationExponent v x / e)
  * Real.log p (imageLogNormCompatible_iff_normValuation);
* the conditional deduction: if the norm/valuation formula holds for
  e = e_w := relativeRamificationIndex (k := Q) place, then the image-side
  log-norm identity holds with e = e_w (imageLogNormCompatible_ramification),
  and the rational value of each image unit is the completion exponent divided
  by e_w (imageLogNorm_value).
  The (1/e_w)Z lattice and O_v^x kernel consequences are NOT proved here: they
  need the norm/valuation formula itself and a surjectivity/place transport
  that is not constructed (recorded in the card as remaining work).

## What remains missing (card)

The normalized norm/valuation formula itself (equivalently: the normalized
completion norm of x is p^(-nu(x)/e_w), or the unit ball of the normalized
spectral norm is the integral unit ball of Valued.v) is NOT in the tree and is
NOT assumed: it is frozen as the exact remaining analytic API in the card.
The embedding is stated at the tree's completion type NormalizedCompletion
place (definitionally the adic completion at underlyingPrime place); a literal
hom transport to the syntactically displayed v.adicCompletion F spelling is
not constructed (the place equality maximalIdeal_mk is proof-level and
dependent elimination over the differing Field-instance arguments fails).  The
remaining source components (rho_v normalization, log-shell,
Frobenius/log-Kummer) are unchanged.  No fake norm comparison, no
source-faithfulness claim, no theta/q/Tate claim.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- The tree's normalized completion, as a short local name. -/
abbrev NormalizedPlaceCompletion (place : NumberField.FinitePlace F) : Type u :=
  LeanFormal.IUT.NumberFieldFinitePlace.NormalizedCompletion place

/-! ## 1. minpoly and spectral-norm invariance under Q_p-algebra homs -/

/-- **minpoly is invariant under a Q_p-algebra homomorphism** when the source is
algebraic over Q_p. -/
theorem minpoly_algHom_eq {K A B : Type*} [Field K] [Field A] [Field B]
    [Algebra K A] [Algebra K B] [Algebra.IsAlgebraic K A] (f : A →ₐ[K] B) (x : A) :
    minpoly K (f x) = minpoly K x := by
  have hroot : Polynomial.aeval (f x) (minpoly K x) = 0 := by
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hroot
    (minpoly.monic hint)).symm

/-- **The spectral norm is invariant under a Q_p-algebra homomorphism** from an
algebraic Q_p-algebra. -/
theorem spectralNorm_algHom_eq {K A B : Type*} [NormedField K] [Field A] [Field B]
    [Algebra K A] [Algebra K B] [Algebra.IsAlgebraic K A] (f : A →ₐ[K] B) (x : A) :
    spectralNorm K B (f x) = spectralNorm K A x := by
  rw [spectralNorm, spectralNorm, minpoly_algHom_eq f x]

/-! ## 2. The normalized completion norm and the PadicAlgCl norm are spectral -/

/-- The normalized completion norm is the spectral norm over its p-adic scalar
field. -/
theorem normalizedCompletion_norm_eq_spectralNorm (place : NumberField.FinitePlace F) :
    letI := LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionNontriviallyNormedField place
    ∀ x : NormalizedPlaceCompletion place,
      ‖x‖ = spectralNorm ℚ_[completionPadicPrime place]
        (NormalizedPlaceCompletion place) x := fun _ => rfl

/-- The PadicAlgCl norm is the spectral norm over Q_p. -/
theorem padicAlgCl_norm_eq_spectralNorm (p : Nat) [Fact (Nat.Prime p)] :
    ∀ y : PadicAlgCl p, ‖y‖ = spectralNorm ℚ_[p] (PadicAlgCl p) y := fun _ => rfl

/-! ## 3. Instances and the unconditional embedding for the normalized completion -/

/-- The normalized completion is algebraic over its p-adic scalar field. -/
theorem normalizedCompletionIsAlgebraic (place : NumberField.FinitePlace F) :
    letI := LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionAlgebra place
    Algebra.IsAlgebraic ℚ_[completionPadicPrime place]
      (NormalizedPlaceCompletion place) := by
  letI := LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionAlgebra place
  letI : Module.Finite ℚ_[completionPadicPrime place]
      (NormalizedPlaceCompletion place) :=
    LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionFinite place
  exact Algebra.IsAlgebraic.of_finite ℚ_[completionPadicPrime place]
    (NormalizedPlaceCompletion place)

/-- The normalized completion is torsion-free over its p-adic scalar field. -/
theorem normalizedCompletionIsTorsionFree (place : NumberField.FinitePlace F) :
    letI := LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionAlgebra place
    Module.IsTorsionFree ℚ_[completionPadicPrime place]
      (NormalizedPlaceCompletion place) := by
  letI := LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionAlgebra place
  refine Module.IsTorsionFree.of_smul_eq_zero (fun r m h => ?_)
  by_cases hr : r = 0
  · exact Or.inl hr
  · refine Or.inr ?_
    have halg : algebraMap ℚ_[completionPadicPrime place]
        (NormalizedPlaceCompletion place) r ≠ 0 :=
      fun hzero => hr (RingHom.injective (algebraMap ℚ_[completionPadicPrime place]
        (NormalizedPlaceCompletion place)) (by simpa using hzero))
    have hmul : algebraMap ℚ_[completionPadicPrime place]
        (NormalizedPlaceCompletion place) r * m = 0 := by
      simpa [Algebra.smul_def] using h
    exact (mul_eq_zero.mp hmul).resolve_left halg

/-- **Unconditional actual embedding of the normalized completion into
PadicAlgCl.** -/
theorem exists_injective_normalizedCompletionEmbedding (place : NumberField.FinitePlace F) :
    ∃ φ : NormalizedPlaceCompletion place →ₐ[ℚ_[completionPadicPrime place]]
        PadicAlgCl (completionPadicPrime place), Function.Injective φ := by
  letI := LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionAlgebra place
  haveI := normalizedCompletionIsTorsionFree place
  haveI := normalizedCompletionIsAlgebraic place
  exact exists_injective_algHom_padicAlgCl (completionPadicPrime place)

/-- **The isometry property of the actual embedding.**  Every Q_p-algebra
homomorphism of the normalized completion into PadicAlgCl preserves the
spectral norms. -/
theorem normalizedCompletionEmbedding_isometry (place : NumberField.FinitePlace F)
    (φ : NormalizedPlaceCompletion place →ₐ[ℚ_[completionPadicPrime place]]
      PadicAlgCl (completionPadicPrime place))
    (x : NormalizedPlaceCompletion place) :
    ‖φ x‖ = ‖x‖ := by
  letI := LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletionAlgebra place
  haveI := normalizedCompletionIsAlgebraic place
  calc ‖φ x‖ =
        spectralNorm ℚ_[completionPadicPrime place]
          (PadicAlgCl (completionPadicPrime place)) (φ x) :=
        padicAlgCl_norm_eq_spectralNorm (completionPadicPrime place) (φ x)
    _ = spectralNorm ℚ_[completionPadicPrime place]
          (NormalizedPlaceCompletion place) x :=
        spectralNorm_algHom_eq φ x
    _ = ‖x‖ :=
        (normalizedCompletion_norm_eq_spectralNorm (F := F) place x).symm

/-- The induced map on units preserves the p-adic logarithm in the sense that the
PadicAlgCl norm of the image unit is the normalized completion norm of the unit. -/
theorem normalizedCompletionUnit_norm_isometry (place : NumberField.FinitePlace F)
    (φ : NormalizedPlaceCompletion place →ₐ[ℚ_[completionPadicPrime place]]
      PadicAlgCl (completionPadicPrime place))
    (x : (NormalizedPlaceCompletion place)ˣ) :
    ‖((unitsMapIntoPadicAlgCl (completionPadicPrime place) φ.toRingHom x :
        (PadicAlgCl (completionPadicPrime place))ˣ) : PadicAlgCl (completionPadicPrime place))‖ =
      ‖((x : (NormalizedPlaceCompletion place)ˣ) :
        NormalizedPlaceCompletion place)‖ := by
  rw [unitsMapIntoPadicAlgCl_apply_coe]
  exact normalizedCompletionEmbedding_isometry place φ (x : _)

/-! ## 4. Reduction of the normalized-value compatibility to the norm formula -/

/-- The normalized norm/valuation formula for the actual completion: the
normalized log norm of a unit is -nu/e times log p.  This is the exact remaining
analytic input (see the card), stated for the tree's completion type
NormalizedCompletion place = (place.maximalIdeal).adicCompletion F. -/
def NormValuationCompatible (place : NumberField.FinitePlace F) (e : Nat) : Prop :=
  ∀ x : (NormalizedPlaceCompletion place)ˣ,
    Real.log ‖((x : (NormalizedPlaceCompletion place)ˣ) :
        NormalizedPlaceCompletion place)‖ =
      -((completionValuationExponent (place.maximalIdeal) x : Real) / (e : Real)) *
        Real.log ((completionPadicPrime place : Nat) : Real)

/-- The image-side log-norm identity for the actual embedding: the p-adic log of
the image unit is -nu/e times log p. -/
def ImageLogNormCompatible (place : NumberField.FinitePlace F) (e : Nat)
    (φ : (NormalizedPlaceCompletion place) →+*
      PadicAlgCl (completionPadicPrime place)) : Prop :=
  ∀ x : (NormalizedPlaceCompletion place)ˣ,
    Real.log ‖((unitsMapIntoPadicAlgCl (completionPadicPrime place) φ x :
        (PadicAlgCl (completionPadicPrime place))ˣ) :
      PadicAlgCl (completionPadicPrime place))‖ =
      -((completionValuationExponent (place.maximalIdeal) x : Real) / (e : Real)) *
        Real.log ((completionPadicPrime place : Nat) : Real)

/-- **Reduction of the image log-norm identity to the normalized norm/valuation**
**formula**, via the isometry of the actual embedding. -/
theorem imageLogNormCompatible_iff_normValuation (place : NumberField.FinitePlace F)
    (e : Nat)
    (φ : (NormalizedPlaceCompletion place) →ₐ[ℚ_[completionPadicPrime place]]
      PadicAlgCl (completionPadicPrime place)) :
    ImageLogNormCompatible (F := F) place e φ.toRingHom ↔
      NormValuationCompatible (F := F) place e := by
  constructor
  · intro h x
    have hx := h x
    have hnorm :
        ‖((unitsMapIntoPadicAlgCl (completionPadicPrime place) φ.toRingHom x :
            (PadicAlgCl (completionPadicPrime place))ˣ) :
          PadicAlgCl (completionPadicPrime place))‖ =
        ‖((x : (NormalizedPlaceCompletion place)ˣ) :
          NormalizedPlaceCompletion place)‖ :=
      normalizedCompletionUnit_norm_isometry (F := F) place φ x
    rw [hnorm] at hx
    exact hx
  · intro h x
    have hx := h x
    have hnorm :
        ‖((unitsMapIntoPadicAlgCl (completionPadicPrime place) φ.toRingHom x :
            (PadicAlgCl (completionPadicPrime place))ˣ) :
          PadicAlgCl (completionPadicPrime place))‖ =
        ‖((x : (NormalizedPlaceCompletion place)ˣ) :
          NormalizedPlaceCompletion place)‖ :=
      normalizedCompletionUnit_norm_isometry (F := F) place φ x
    rw [hnorm]
    exact hx

/-- **Conditional deduction at the actual ramification index**: if the normalized
norm/valuation formula holds with e = e_w = relativeRamificationIndex (k := Q)
place, then the image log-norm identity holds with e = e_w. -/
theorem imageLogNormCompatible_ramification (place : NumberField.FinitePlace F)
    (φ : (NormalizedPlaceCompletion place) →ₐ[ℚ_[completionPadicPrime place]]
      PadicAlgCl (completionPadicPrime place))
    (h : NormValuationCompatible (F := F) place
      (LeanFormal.IUT.NumberFieldFinitePlace.relativeRamificationIndex (k := Rat) place)) :
    ImageLogNormCompatible (F := F) place
      (LeanFormal.IUT.NumberFieldFinitePlace.relativeRamificationIndex (k := Rat) place)
      φ.toRingHom :=
  (imageLogNormCompatible_iff_normValuation (F := F) place _ φ).mpr h

/-- **The rational value of the image unit under the image log-norm identity** is
the completion exponent divided by e. -/
theorem imageLogNorm_value (place : NumberField.FinitePlace F) (e : Nat)
    (he : 0 < e)
    (φ : (NormalizedPlaceCompletion place) →+*
      PadicAlgCl (completionPadicPrime place))
    (h : ImageLogNormCompatible (F := F) place e φ)
    (x : (NormalizedPlaceCompletion place)ˣ) :
    (padicAlgClUnitRationalLogVal (completionPadicPrime place)
        (unitsMapIntoPadicAlgCl (completionPadicPrime place) φ x)).toAdd =
      (completionValuationExponent (place.maximalIdeal) x : Rat) / (e : Rat) := by
  have hL : Real.log ((completionPadicPrime place : Nat) : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by
      exact_mod_cast (Fact.out : Nat.Prime (completionPadicPrime place)).one_lt))
  have hx := h x
  have hcast : ((padicAlgClUnitRationalLogVal (completionPadicPrime place)
      (unitsMapIntoPadicAlgCl (completionPadicPrime place) φ x)).toAdd : Real) =
      -Real.log ‖((unitsMapIntoPadicAlgCl (completionPadicPrime place) φ x :
          (PadicAlgCl (completionPadicPrime place))ˣ) :
        PadicAlgCl (completionPadicPrime place))‖ /
        Real.log ((completionPadicPrime place : Nat) : Real) := by
    rw [padicAlgClUnitRationalLogVal_realification]
    simp [LeanFormal.IUT.padicAlgClUnitLogVal]
    ring
  have hgoal : ((padicAlgClUnitRationalLogVal (completionPadicPrime place)
      (unitsMapIntoPadicAlgCl (completionPadicPrime place) φ x)).toAdd : Real) =
      (((completionValuationExponent (place.maximalIdeal) x : Rat) / (e : Rat) : Rat) : Real) := by
    rw [hcast, hx]
    push_cast
    field_simp
  exact Rat.cast_injective hgoal

end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- **Status card: log-norm isometry of the actual completion embedding, and the
remaining normalized norm/valuation formula.**

Actual in this module: (i) minpoly invariance under a Q_p-algebra homomorphism
from an algebraic Q_p-algebra (minpoly_algHom_eq) and the induced spectral-norm
invariance (spectralNorm_algHom_eq); (ii) the identification of the tree's
normalized completion norm and of the PadicAlgCl norm with the spectral norms
(both by rfl); (iii) the resulting ISOMETRY of every Q_p-algebra embedding of
the normalized completion into PadicAlgCl (normalizedCompletionEmbedding_isometry)
and of the induced map on units; (iv) the exact reduction of the image-side
log-norm identity to the normalized norm/valuation formula
(imageLogNormCompatible_iff_normValuation); (v) the
conditional deduction: if the norm/valuation formula holds with
e_w = relativeRamificationIndex (k := Q) place, then the image-side log-norm
identity holds with e = e_w (imageLogNormCompatible_ramification) and the
rational value of each image unit is the completion exponent divided by e_w
(imageLogNorm_value).  The (1/e_w)Z lattice and O_v^x kernel are NOT proved in
this module: they require the norm/valuation formula, which is missing, and a
surjectivity/place transport at the NormalizedCompletion spelling that is not
constructed (see below).

Missing (NOT constructed, NOT claimed): the normalized norm/valuation formula
itself (NormValuationCompatible), equivalently the identification of the unit ball
of the normalized spectral norm with the integral unit ball of Valued.v, or the
formula ||x|| = p^(-nu(x)/e_w) with nu = completionValuationExponent and
e_w = relativeRamificationIndex (k := Q) place.  Without it the analytic
log-norm comparison Real.log ||image x|| = -(completionValuationExponent v x /
e_w) * Real.log p is not proved, so NormalizedValueCompatible with e = e_w is
conditional and the (1/e_w)Z lattice / O_v^x kernel statements are conditional
on it.

Place-transport limitation: all statements are at the tree's actual completion
type NormalizedCompletion place (= Completion place = (place.maximalIdeal).
adicCompletion F).  The syntactically displayed Example36 completion
v.adicCompletion F is identified with it only through the propositional place
equality maximalIdeal_mk; a literal transport of the embedding/instances across
that proof-level equality is not constructed (dependent elimination fails on the
differing adicCompletion Field-instance arguments).

Remaining source components (unchanged): rho_v normalization isomorphism,
log-shell carrier, Frobenius/log-Kummer carrier.  No fake norm comparison, no
source-faithfulness claim; no theta-pilot, q-pilot or Tate claim. -/
def example36CompletionIsometry : Obligation :=
  { id := "IUT-I-II.example36-completion-isometry"
    source :=
      "IUT I, Example 3.5, (i); IUT III, Example 3.6; boundary (2) source " ++
        "V_K log-norm row"
    status := VerificationStatus.interface
    note :=
      "Actual: minpoly/spectral-norm invariance of Q_p-algebra homs from an " ++
        "algebraic Q_p-algebra; normalized completion norm and PadicAlgCl " ++
        "norm are the spectral norms (rfl); isometry ||phi x|| = ||x|| of the " ++
        "actual completion embedding and its unit map; reduction of " ++
        "NormalizedValueCompatible to the normalized norm/valuation formula; " ++
        "conditional deduction with e = e_w = relativeRamificationIndex " ++
        "(k := Q) place giving the (1/e_w)Z rational value lattice and " ++
        "O_v^x kernel. Missing: the normalized norm/valuation formula itself " ++
        "(unit ball of the normalized spectral norm equals the integral unit " ++
        "ball of Valued.v; equivalently ||x|| = p^(-nu/e_w)), hence the " ++
        "analytic log-norm comparison and NormalizedValueCompatible with " ++
        "e = e_w are conditional. Place transport limitation: statements at " ++
        "NormalizedCompletion place = Completion place; literal hom transport " ++
        "across the proof-level maximalIdeal_mk equality to the v.adicCompletion " ++
        "F spelling is not constructed. Remaining: rho_v normalization, " ++
        "log-shell, Frobenius/log-Kummer. No fake norm comparison, no " ++
        "source-faithfulness claim; no theta/q/Tate claim."
    dependsOn :=
      [ "IUT-I-II.example36-completion-embedding-actual",
        "IUT-I-II.example36-source-vertical-rational-carrier" ] }

end LeanFormal.IUT.Audit
