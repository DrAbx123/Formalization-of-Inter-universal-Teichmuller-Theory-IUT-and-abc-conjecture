import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveEtaleCovers
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic

/-!
# Foundation F3c: actual irreducibility and connectedness of the curve

This module continues Example36CurveScheme and Example36CurveEtaleCovers.  It proves
that the affine coordinate ring K[x,y]/(y^2 - x^3 + x) is a domain, hence that the
actual affine curve scheme curveScheme K = Spec R is irreducible and connected, and
that the two-punctured EXTRA open subscheme curveTwoPuncturedScheme K = E \\ {O,P} is
nonempty, open in an irreducible space, hence irreducible and connected.  The
once-punctured source is curveScheme K itself (E \\ {O}); the extra puncture at
the finite 2-torsion point P = (0,0) is not a source object.  It then records which fields
of the frozen SchemeGaloisConnectednessCard of Example36CurveEtaleCovers are now
actual (the scheme-level geometric connectedness) and which remain missing
(the Galois category, its fiber functor and the etale fundamental group).

## What is actually proved here

* the polynomial y^2 - x^3 + x is irreducible in K[x,y] (equivalent to the quadratic
  t^2 - (x^3 - x) over K[x], which has no root because x^3 - x has odd degree);
* hence the coordinate ring is a domain (prime principal ideal in a UFD);
* Spec of a domain is irreducible (Mathlib instance) and connected;
* the punctured curve is nonempty, and is an open subscheme of an irreducible
  space, hence irreducible and connected;
* the geometric-connectedness field of SchemeGaloisConnectednessCard is actual;
  the Galois-category/fiber-functor/fundamental-group fields remain frozen cards.

No fake scheme, no fake Galois category, no fake topology.  No theta/q-pilot/Tate
claim is made.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

universe u

variable {K : Type u} [Field K]

/-! ## 1. The quadratic form of the equation over K[x] -/

/-- The coindex type of the variable y = X 1 (it has a unique element). -/
abbrev curveComplementIndex : Type := {j : Fin 2 // j ≠ (1 : Fin 2)}

instance curveComplementIndex_unique : Unique curveComplementIndex where
  default := ⟨0, by decide⟩
  uniq j := by
    apply Subtype.ext
    apply Fin.ext
    change (j.1.val : ℕ) = 0
    have hne : j.1.val ≠ 1 := by
      intro hh
      exact j.2 (Fin.ext hh)
    have hlt : j.1.val < 2 := j.1.isLt
    omega

/-- The equation y^2 - x^3 + x as a quadratic in y over K[x]. -/
def curveQuadraticPolynomial : Polynomial (MvPolynomial curveComplementIndex K) :=
  Polynomial.X ^ 2 - Polynomial.C (MvPolynomial.X (default : curveComplementIndex) ^ 3 -
    MvPolynomial.X (default : curveComplementIndex))

/-- The coordinate polynomial viewed as a quadratic in y over K[x]: this is the
algebra equivalence induced by renaming x to the coefficient variable and y to the
polynomial variable, followed by the standard left-option equivalence. -/
noncomputable def curveEquationAlgEquiv :
    MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (MvPolynomial curveComplementIndex K) :=
  (MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe (1 : Fin 2)).symm).trans
    (MvPolynomial.optionEquivLeft K curveComplementIndex)

theorem curveEquationAlgEquiv_apply :
    curveEquationAlgEquiv (K := K) (curveEquationPolynomial K) =
      curveQuadraticPolynomial (K := K) := by
  simp only [curveEquationAlgEquiv, curveEquationPolynomial, curveQuadraticPolynomial,
    AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.optionEquivLeft_apply,
    MvPolynomial.rename_X, MvPolynomial.aeval_X, map_add, map_sub, map_pow]
  have h1 : (Equiv.optionSubtypeNe (1 : Fin 2)).symm (1 : Fin 2) = none := by
    rw [Equiv.optionSubtypeNe_symm_apply]
    exact dif_pos rfl
  have h0 : (Equiv.optionSubtypeNe (1 : Fin 2)).symm (0 : Fin 2) =
      some (⟨0, by decide⟩ : curveComplementIndex) := by
    rw [Equiv.optionSubtypeNe_symm_apply]
    rw [dif_neg (by decide : (0 : Fin 2) ≠ 1)]
  simp only [h0, h1, Option.elim_none, Option.elim_some]
  have hdef : (⟨0, by decide⟩ : curveComplementIndex) = default := rfl
  simp only [hdef]
  ring


/-! ## 2. Irreducibility of the coordinate polynomial -/

/-- Irreducibility of the quadratic t^2 - (x^3 - x) over K[x]: no root exists,
because x^3 - x has odd degree while a square has even degree. -/
theorem curveQuadraticPolynomial_irreducible :
    Irreducible (curveQuadraticPolynomial (K := K)) := by
  have hmonic : (curveQuadraticPolynomial (K := K)).Monic := by
    unfold curveQuadraticPolynomial
    exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hdeg2 : (curveQuadraticPolynomial (K := K)).natDegree = 2 := by
    unfold curveQuadraticPolynomial
    rw [Polynomial.natDegree_X_pow_sub_C]
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic
    (by rw [hdeg2]) (by rw [hdeg2]; norm_num)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  rw [Polynomial.mem_roots hmonic.ne_zero] at hr
  have hroot : r ^ 2 = MvPolynomial.X (default : curveComplementIndex) ^ 3 -
      MvPolynomial.X (default : curveComplementIndex) := by
    have h := hr
    unfold curveQuadraticPolynomial at h
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at h
    linear_combination h
  have hroot' : (MvPolynomial.uniqueAlgEquiv K curveComplementIndex r) ^ 2 =
      Polynomial.X ^ 3 - Polynomial.X := by
    have h := congrArg (MvPolynomial.uniqueAlgEquiv K curveComplementIndex) hroot
    simpa [map_pow, map_sub, MvPolynomial.uniqueAlgEquiv_apply] using h
  have hdeg3 : (Polynomial.X ^ 3 - Polynomial.X : Polynomial K).natDegree = 3 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simp
  have hsq : (MvPolynomial.uniqueAlgEquiv K curveComplementIndex r ^ 2).natDegree = 3 := by
    rw [hroot', hdeg3]
  by_cases hr0 : MvPolynomial.uniqueAlgEquiv K curveComplementIndex r = 0
  · have hzero : (Polynomial.X ^ 3 - Polynomial.X : Polynomial K) = 0 := by
      rw [← hroot', hr0]
      simp
    have := congrArg Polynomial.natDegree hzero
    rw [hdeg3, Polynomial.natDegree_zero] at this
    omega
  · have hlead : Polynomial.leadingCoeff
        (MvPolynomial.uniqueAlgEquiv K curveComplementIndex r) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Polynomial.leadingCoeff_ne_zero.mpr hr0)
    rw [Polynomial.natDegree_pow' hlead] at hsq
    omega

/-- The coordinate polynomial y^2 - x^3 + x is irreducible in K[x,y]. -/
theorem curveEquationPolynomial_irreducible :
    Irreducible (curveEquationPolynomial K) := by
  have hq : Irreducible (curveQuadraticPolynomial (K := K)) :=
    curveQuadraticPolynomial_irreducible
  have hep : Irreducible (curveEquationAlgEquiv (K := K) (curveEquationPolynomial K)) := by
    rw [curveEquationAlgEquiv_apply]
    exact hq
  exact (MulEquiv.irreducible_iff (f := curveEquationAlgEquiv (K := K))).mp hep

/-- The coordinate polynomial is prime, since MvPolynomial over a field is a UFD. -/
theorem curveEquationPolynomial_prime : Prime (curveEquationPolynomial K) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp curveEquationPolynomial_irreducible

/-- **The affine coordinate ring is a domain.** -/
instance curveCoordinateRing_isDomain : IsDomain (curveCoordinateRing K) := by
  have hI : (curveCoordinateIdeal K).IsPrime := by
    rw [curveCoordinateIdeal]
    exact Ideal.isPrime_span_singleton_of_prime (curveEquationPolynomial_prime (K := K))
  exact (Ideal.Quotient.isDomain_iff_prime (curveCoordinateIdeal K)).mpr hI

/-! ## 3. Irreducible and connected curve scheme -/

/-- The affine curve scheme is irreducible (Spec of a domain). -/
instance curveScheme_irreducibleSpace : IrreducibleSpace (curveScheme K) :=
  inferInstance

/-- The affine curve scheme is connected. -/
instance curveScheme_connectedSpace : ConnectedSpace (curveScheme K) :=
  inferInstance

/-! ## 4. The punctured curve is nonempty, irreducible and connected -/

/-- Evaluation at the rational point (1,0) of the curve. -/
abbrev curveOneZeroPolynomialEval (K : Type u) [Field K] :
    MvPolynomial (Fin 2) K →+* K :=
  MvPolynomial.eval (fun i : Fin 2 => if i = (0 : Fin 2) then (1 : K) else 0)

/-- The evaluation at (1,0) factors through the coordinate ring. -/
abbrev curveOneZeroEval (K : Type u) [Field K] : curveCoordinateRing K →+* K :=
  Ideal.Quotient.lift (curveCoordinateIdeal K) (curveOneZeroPolynomialEval K) (by
    intro a ha
    have hle : curveCoordinateIdeal K ≤ RingHom.ker (curveOneZeroPolynomialEval K) := by
      rw [curveCoordinateIdeal, Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      change curveOneZeroPolynomialEval K (curveEquationPolynomial K) = 0
      simp [curveOneZeroPolynomialEval, curveEquationPolynomial]
    exact hle ha)

theorem curveOneZeroEval_surjective (K : Type u) [Field K] :
    Function.Surjective (curveOneZeroEval K) := by
  intro y
  refine ⟨Ideal.Quotient.mk (curveCoordinateIdeal K) (MvPolynomial.C y), ?_⟩
  rw [curveOneZeroEval, Ideal.Quotient.lift_mk]
  simp [curveOneZeroPolynomialEval]

/-- The ideal of the point (1,0). -/
abbrev curveOneZeroIdeal (K : Type u) [Field K] : Ideal (curveCoordinateRing K) :=
  RingHom.ker (curveOneZeroEval K)

noncomputable instance curveOneZeroIdeal_isMaximal (K : Type u) [Field K] :
    (curveOneZeroIdeal K).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (curveOneZeroEval K) (curveOneZeroEval_surjective K)

/-- The point (1,0) of the curve. -/
abbrev curveOneZeroPoint (K : Type u) [Field K] : curveScheme K :=
  ⟨curveOneZeroIdeal K, (curveOneZeroIdeal_isMaximal K).isPrime⟩

theorem curveOneZeroIdeal_ne_originIdeal (K : Type u) [Field K] :
    curveOneZeroIdeal K ≠ curveOriginIdeal K := by
  intro hEq
  have hx : curveX K ∈ curveOriginIdeal K := by
    rw [curveOriginIdeal, RingHom.mem_ker]
    simp [curveOriginEval, curveX, curveOriginPolynomialEval]
  have hx' : curveX K ∈ curveOneZeroIdeal K := by
    rw [hEq]
    exact hx
  have hzero : curveOneZeroEval K (curveX K) = 0 := by
    rw [curveOneZeroIdeal, RingHom.mem_ker] at hx'
    exact hx'
  have hone : curveOneZeroEval K (curveX K) = 1 := by
    simp [curveOneZeroEval, curveX, curveOneZeroPolynomialEval]
  rw [hone] at hzero
  exact one_ne_zero hzero

theorem curveOneZeroPoint_ne_originPoint (K : Type u) [Field K] :
    curveOneZeroPoint K ≠ curveOriginPoint K := by
  intro h
  exact curveOneZeroIdeal_ne_originIdeal K
    (congrArg (fun x : PrimeSpectrum (curveCoordinateRing K) => x.asIdeal) h)

instance curveTwoPuncturedScheme_nonempty : Nonempty (curveTwoPuncturedScheme K) := by
  refine ⟨?_, ?_⟩
  · exact curveOneZeroPoint K
  · change curveOneZeroPoint K ∈ ({curveOriginPoint K} : Set (curveScheme K))ᶜ
    simp [curveOneZeroPoint_ne_originPoint]

/-- The punctured curve is irreducible: it is the open subset (via an open
embedding) of the irreducible curve scheme. -/
instance curveTwoPuncturedScheme_irreducibleSpace : IrreducibleSpace (curveTwoPuncturedScheme K) :=
  (inferInstance : IsOpenImmersion (curveTwoPuncturedOpenMap K)).base_open.irreducibleSpace

/-- The punctured curve is connected. -/
instance curveTwoPuncturedScheme_connectedSpace : ConnectedSpace (curveTwoPuncturedScheme K) :=
  inferInstance


/-! ## 5. Connection to SchemeGaloisConnectednessCard: once-punctured source vs two-punctured extra -/

/-- Explicit restatement of irreducibility of the ONCE-punctured affine source E \\ {O}. -/
theorem curveScheme_irreducible : IrreducibleSpace (curveScheme K) :=
  inferInstance

/-- Explicit restatement of connectedness of the ONCE-punctured affine source E \\ {O}. -/
theorem curveScheme_connected : ConnectedSpace (curveScheme K) :=
  inferInstance

/-- Explicit restatement of irreducibility of the TWO-punctured EXTRA curve E \\ {O,P}. -/
theorem curveTwoPuncturedScheme_irreducible :
    IrreducibleSpace (curveTwoPuncturedScheme K) :=
  inferInstance

/-- Explicit restatement of connectedness of the TWO-punctured EXTRA curve E \\ {O,P}. -/
theorem curveTwoPuncturedScheme_connected : ConnectedSpace (curveTwoPuncturedScheme K) :=
  inferInstance

/-- The **geometric-connectedness field** of SchemeGaloisConnectednessCard for the
ONCE-punctured source E \\ {O} = curveScheme K. -/
def CurveOncePuncturedGeometricConnectedness (K : Type u) [Field K] : Prop :=
  IrreducibleSpace (curveScheme K) ∧ ConnectedSpace (curveScheme K)

/-- **The geometric-connectedness field of the once-punctured source card is actual.** -/
theorem curveOncePuncturedGeometricConnectedness_actual (K : Type u) [Field K] :
    CurveOncePuncturedGeometricConnectedness K :=
  ⟨inferInstance, inferInstance⟩

/-- The geometric-connectedness field for the TWO-punctured EXTRA curve E \\ {O,P};
this is not the source curve object. -/
def CurveTwoPuncturedGeometricConnectedness (K : Type u) [Field K] : Prop :=
  Nonempty (curveTwoPuncturedScheme K) ∧
    IrreducibleSpace (curveTwoPuncturedScheme K) ∧
      ConnectedSpace (curveTwoPuncturedScheme K)

/-- **The geometric-connectedness field of the two-punctured extra object is actual.** -/
theorem curveTwoPuncturedGeometricConnectedness_actual (K : Type u) [Field K] :
    CurveTwoPuncturedGeometricConnectedness K :=
  ⟨curveTwoPuncturedScheme_nonempty, curveTwoPuncturedScheme_irreducible,
    curveTwoPuncturedScheme_connected⟩

/-- Legacy name for the two-punctured extra geometric-connectedness field; it is
explicitly NOT the once-punctured source field. -/
abbrev CurveSchemeGeometricConnectedness (K : Type u) [Field K] : Prop :=
  CurveTwoPuncturedGeometricConnectedness K

theorem curveSchemeGeometricConnectedness_actual (K : Type u) [Field K] :
    CurveSchemeGeometricConnectedness K :=
  curveTwoPuncturedGeometricConnectedness_actual K

/-- The remaining fields of SchemeGaloisConnectednessCard for the TWO-punctured
EXTRA curve E \\ {O,P}. -/
def CurveTwoPuncturedGaloisConnectednessRemainingFields (K : Type u) [Field K] : Prop :=
  SchemeGaloisConnectednessCardRealized (curveTwoPuncturedScheme K)

/-- The remaining fields of SchemeGaloisConnectednessCard for the ONCE-punctured
SOURCE curve E \\ {O} = curveScheme K. -/
def CurveOncePuncturedGaloisConnectednessRemainingFields (K : Type u) [Field K] : Prop :=
  SchemeGaloisConnectednessCardRealized (curveScheme K)

/-- The field audit for the once-punctured source: the geometric-connectedness
field is actual, the Galois-category/fiber-functor/fundamental-group fields remain
frozen. -/
theorem curveOncePuncturedGaloisConnectednessCard_geometricField_actual (K : Type u)
    [Field K] : CurveOncePuncturedGeometricConnectedness K :=
  curveOncePuncturedGeometricConnectedness_actual K

/-- The field audit for the two-punctured extra object (not the source). -/
theorem curveTwoPuncturedGaloisConnectednessCard_geometricField_actual (K : Type u)
    [Field K] : CurveTwoPuncturedGeometricConnectedness K :=
  curveTwoPuncturedGeometricConnectedness_actual K

end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- **Status card: actual geometric connectedness of the once-punctured source curve.**

Actual in Example36CurveConnectedness: the coordinate polynomial y^2 - x^3 + x is
irreducible, the coordinate ring K[x,y]/(y^2 - x^3 + x) is a domain, the once-punctured
source curveScheme K = E \\ {O} is irreducible and connected, and the two-punctured
EXTRA open subscheme curveTwoPuncturedScheme K = E \\ {O,P} is nonempty, open in an
irreducible space, hence irreducible and connected.  The geometric-connectedness field
of SchemeGaloisConnectednessCard is therefore actual for the once-punctured source, and
separately for the two-punctured extra object.
Remaining fields of that card (NOT constructed, NOT claimed): the Galois category
structure on finite etale covers, a fiber functor, the arithmetic and geometric etale
fundamental groups.  No fake Galois category, no fake topology; no theta/q/Tate claim. -/
def curveSchemeGeometricConnectednessCard : Obligation :=
  { id := "IUT-I-II.example36-curve-geometric-connectedness"
    source := "IUT I/II, D6 curve-Pi input; foundation item F3c"
    status := VerificationStatus.proved
    note := "Actual: coordinate polynomial y^2 - x^3 + x irreducible; coordinate ring a domain; once-punctured source curveScheme K = E \\ {O} irreducible and connected; two-punctured extra curveTwoPuncturedScheme K = E \\ {O,P} nonempty, irreducible and connected; the two geometric-connectedness fields are separated. Remaining fields of SchemeGaloisConnectednessCard: Galois category, fiber functor, arithmetic and geometric etale fundamental groups. The two-punctured extra is not the source. No fake Galois category or topology; no theta/q/Tate claim."
    dependsOn :=
      [ "IUT-I-II.example36-curve-scheme",
        "IUT-I-II.example36-curve-etale-covers" ] }

end LeanFormal.IUT.Audit
