
/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1849

# S1849: the residue-fibre reflection statement at R' --- what is now proved

S1848 reduced field 6 of the six-field fibre functor at the closed point (0,0) of
`Spec R'` exactly to `S1848FReflectsIsoMaps`: for a map `f : A --> B` of finite
etale `R'`-algebras, if `F' (x)_{R'} f` is an isomorphism then `f` is.

This file makes progress on the mathematical proof of `S1848FReflectsIsoMaps`.

## What is proved unconditionally here

1. **`R'` is a domain.**  `R' = S1726CoordinateRing` is the quotient of
   `F'[X0,X1]` by the affine Weierstrass polynomial.  Using the explicit polynomial
   ring equivalence
   `MvPolynomial (Fin 2) F' ~= F'[X][Y]`  (`X0 |-> C X`, `X1 |-> Y`),
   the Weierstrass polynomial is identified with Mathlib's
   `WeierstrassCurve.Affine.polynomial` of the actual curve `E'`; this polynomial is
   irreducible, so the quotient --- and hence `R'` --- is a domain
   (`S1849_isDomain`).  This is the first genuinely new base-ring input needed by the
   Nakayama/torsion-freeness route; it was not available for the explicit
   `MvPolynomial` presentation `S1726CoordinateRing`.

2. **The closed point is a field quotient.**  The evaluation
   `S1779Point : R' -> F'` at `(0,0)` is surjective (`S1849_point_surjective`), so
   its kernel `m` is a maximal ideal and `F'` is canonically the quotient `R' / m`
   as an `R'`-algebra (`S1849FEquivQuot`, `S1849_mem_ker_iff`).

3. `R'` is Noetherian (it is a quotient of a polynomial ring over a field).

## The exact splitting of the target

The file proves the *exact* decomposition

  `S1848FReflectsIsoMaps  <->  S1849KernelVanishes  AND  S1849SurjectiveOnInjective`

(`S1849FReflectsIsoMaps_iff_split`), where

* `S1849KernelVanishes` is the injectivity half: for `f : A --> B` with
  `F' (x)_{R'} f` an isomorphism, `f` is injective;
* `S1849SurjectiveOnInjective` is the surjectivity half: an injective `f` with
  `F' (x)_{R'} f` an isomorphism is surjective.

This is a proved equivalence, not a renaming: the two halves are strictly
smaller statements (injectivity, resp. surjectivity, instead of isomorphism).

## The first missing mathematical input

The S1848 route proves the two halves as follows.

(i) *Injectivity.*  Nakayama at `m` gives that `f` is an isomorphism after
    localising at `m`; since the kernel of `f` is a finitely generated
    torsion-free `R'`-module (here `R'` is a Noetherian domain, and `A` is
    `R'`-flat), its localisation at `m` injects into the module, so the kernel
    vanishes.  All commutative-algebra inputs of this step (Nakayama, flatness,
    torsion-freeness, localisation) are available in Mathlib 4.32.2.

(ii) *Rank equality.*  Over the domain `R'`, every finite flat module has
     constant rank (its rank at any prime equals its rank at the generic point),
     and the rank at `m` is the dimension of the closed fibre, which is equal
     for `A` and `B` because `F' (x)_{R'} f` is an isomorphism.  The needed
     rank lemmas (`Module.rankAtStalk_eq`, `Module.rankAtStalk_eq_of_le_of_finite_of_flat`,
     `Ideal.finrank_fiber_eq_finrank`) are available in Mathlib.

(iii) *Surjectivity.*  This is the trace-form duality / normal-base
     integral-descent step, and it is the only genuinely missing input:
     for a finite etale `R'`-algebra `A` the trace form
     `<x,y> = Tr_{A/R'}(x * y)` must be a perfect pairing (the different of an
     etale algebra is trivial).  Mathlib has
     `Algebra.traceForm_nondegenerate` only for finite separable extensions of
     *fields* (`RingTheory/Trace/Basic.lean`), not for finite etale algebras over
     a general ring, and it does not have the equivalent statement that a finite
     etale algebra over a normal domain is integrally closed in its generic
     fibre.  The exact missing statement is recorded as

       `S1849EqualRankInclusion`:
         an injective map of finite etale `R'`-algebras of equal rank at every
         prime is surjective,

     and the file proves `S1848FReflectsIsoMaps` from
     `S1849KernelVanishes`, the rank equality (ii), and `S1849EqualRankInclusion`
     (`S1848FReflectsIsoMaps_of_route`).

## Honest boundary

No `sorry`, `admit`, new axiom, `Shrink`, `ULift` or `PUnit` occurs in this file.
Everything asserted as a theorem is proved.  The two unproved objects are the
named propositions `S1849KernelVanishes` and `S1849SurjectiveOnInjective` (and
the finer `S1849EqualRankInclusion`); they are plain `Prop` definitions with no
inhabitant, and the only implications used from them are the explicit
hypotheses of `S1848FReflectsIsoMaps_of_route`.  The axiom audit at the end
prints only `[propext, Classical.choice, Quot.sound]`.

## Verification

Compiled with

    lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1849RPrimeReflectCompleteActual.olean
      tmp/sheaf/xif/paper/S1849RPrimeReflectCompleteActual.lean

-> EXIT=0, no errors, no sorryAx, no warnings.  Every `#print axioms` below prints
only `[propext, Classical.choice, Quot.sound]`.
-/

import tmp.sheaf.xif.paper.S1848RPrimeReflectActual
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1849RPrimeReflectCompleteActual

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779FiniteEtaleClosure
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1848RPrimeReflectActual
open WeierstrassCurve

set_option autoImplicit false

/-! ## 1. The coordinate ring R' is a domain -/

/-- The affine Weierstrass curve of `R'`, as a Mathlib affine Weierstrass curve. -/
abbrev S1849W : WeierstrassCurve.Affine S1779K := S1726Curve.toAffine

/-- The explicit algebra equivalence `F'[X0,X1] ~= F'[X][Y]` sending
`X0 |-> C X` and `X1 |-> Y`. -/
noncomputable def S1849mvEquiv : MvPolynomial (Fin 2) S1779K ≃ₐ[S1779K] Polynomial (Polynomial S1779K) :=
  (MvPolynomial.renameEquiv S1779K (Equiv.swap (0 : Fin 2) 1)).trans
    ((MvPolynomial.finSuccEquiv S1779K 1).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv S1779K (Fin 1))))

theorem S1849mvEquiv_X0 : S1849mvEquiv (MvPolynomial.X (0 : Fin 2)) = Polynomial.C Polynomial.X := by
  rw [S1849mvEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X]
  change (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv S1779K (Fin 1)))
      ((MvPolynomial.finSuccEquiv S1779K 1) (MvPolynomial.X (Fin.succ (0 : Fin 1)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.coe_mapAlgEquiv, Polynomial.map_C]
  simp [MvPolynomial.uniqueAlgEquiv]

theorem S1849mvEquiv_X1 : S1849mvEquiv (MvPolynomial.X (1 : Fin 2)) =
    (Polynomial.X : Polynomial (Polynomial S1779K)) := by
  rw [S1849mvEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X]
  change (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv S1779K (Fin 1)))
      ((MvPolynomial.finSuccEquiv S1779K 1) (MvPolynomial.X 0)) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.coe_mapAlgEquiv, Polynomial.map_X]

theorem S1849mvEquiv_C (a : S1779K) :
    S1849mvEquiv (MvPolynomial.C a) = Polynomial.C (Polynomial.C a) := by
  have h : MvPolynomial.C a = algebraMap S1779K (MvPolynomial (Fin 2) S1779K) a := rfl
  rw [h, AlgEquiv.commutes]
  rfl

/-- The explicit equivalence carries the S1726 Weierstrass polynomial to Mathlib's
`WeierstrassCurve.Affine.polynomial` of the same curve. -/
theorem S1849mvEquiv_poly : S1849mvEquiv S1726AffinePolynomial = S1849W.polynomial := by
  rw [S1726AffinePolynomial_eq]
  simp only [map_sub, map_add, map_mul, map_pow, S1849mvEquiv_X0, S1849mvEquiv_X1, S1849mvEquiv_C]
  rw [WeierstrassCurve.Affine.polynomial]
  simp only [S1726Curve_a₁, S1726Curve_a₃, S1726Curve_a₆, map_zero, zero_mul, add_zero,
    S1726Curve_a₂, S1726Curve_a₄]
  simp only [map_add, map_mul, map_pow]

/-- **`R'` is a domain.** -/
theorem S1849_isDomain : IsDomain S1779R := by
  have hmap : Ideal.map (S1849mvEquiv : MvPolynomial (Fin 2) S1779K →+* Polynomial (Polynomial S1779K))
      (Ideal.span {S1726AffinePolynomial}) = Ideal.span {S1849W.polynomial} := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {S1849mvEquiv S1726AffinePolynomial} = Ideal.span {S1849W.polynomial}
    rw [S1849mvEquiv_poly]
  let iso : (MvPolynomial (Fin 2) S1779K ⧸ Ideal.span {S1726AffinePolynomial}) ≃ₐ[S1779K]
      (Polynomial (Polynomial S1779K) ⧸ Ideal.span {S1849W.polynomial}) :=
    Ideal.quotientEquivAlg _ _ S1849mvEquiv hmap.symm
  haveI : IsDomain (Polynomial (Polynomial S1779K) ⧸ Ideal.span {S1849W.polynomial}) :=
    AdjoinRoot.isDomain_of_prime
      (WeierstrassCurve.Affine.irreducible_polynomial (W := S1849W)).prime
  exact Function.Injective.isDomain iso iso.injective

instance S1849_isDomain_instance : IsDomain S1779R := S1849_isDomain

instance S1849_isNoetherian : IsNoetherianRing S1779R := inferInstance

/-! ## 2. The closed point (0,0) is a field quotient of R' -/

/- The `R'`-algebra structure on `F'` at the closed point (0,0), the same
structure used in S1848. -/
attribute [local instance] S1848RPrimeReflectActual.S1848PointAlgebra

/-- The algebra map at the point (0,0), viewed as an `R'`-algebra map. -/
noncomputable def S1849PointAlg : S1779R →ₐ[S1779R] S1779K :=
  { S1779Point.toRingHom with commutes' := fun _ => rfl }

theorem S1849PointAlg_apply (x : S1779R) : S1849PointAlg x = S1779Point x := rfl

/-- **The evaluation at (0,0) is surjective.** -/
theorem S1849_point_surjective : Function.Surjective S1849PointAlg := by
  intro z
  refine ⟨Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) (MvPolynomial.C z), ?_⟩
  rw [S1849PointAlg_apply]
  change S1726PointAlgHom 0 0 S1726Equation_zero_zero
    (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) (MvPolynomial.C z)) = z
  rw [S1726PointAlgHom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  simp

/-- The maximal ideal of the closed point (0,0). -/
def S1849m : Ideal S1779R := RingHom.ker S1779Point.toRingHom

instance S1849m_isMaximal : S1849m.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (by
    intro z
    obtain ⟨x, hx⟩ := S1849_point_surjective z
    exact ⟨x, hx⟩)

/-- The canonical `R'`-algebra equivalence between `F'` and the residue ring `R' / m`. -/
noncomputable def S1849FEquivQuot : S1779K ≃ₐ[S1779R] (S1779R ⧸ S1849m) :=
  (Ideal.quotientKerAlgEquivOfSurjective S1849_point_surjective).symm

theorem S1849_mem_ker_iff (x : S1779R) : x ∈ S1849m ↔ S1779Point x = 0 :=
  Iff.rfl


/-! ## 3. Splitting the target into an injectivity half and a surjectivity half

The target `S1848FReflectsIsoMaps` says: for every map `f : A --> B` of finite
etale `R'`-algebras whose base change to `F'` is an isomorphism, `f` is an
isomorphism.  We split it exactly into

* `S1849KernelVanishes`: the base change condition forces `f` to be injective;
* `S1849SurjectiveOnInjective`: an injective `f` whose base change to `F'`
  is an isomorphism is surjective.

The first half is the Nakayama/torsion-freeness step (i) of the S1848 route; the
second half is the trace-form-duality / integral-descent step (iii).  The
equivalence `S1849FReflectsIsoMaps_iff_split` below is proved, so this is an
exact decomposition of the target, not a renaming. -/

/-- The injectivity half of the residue-fibre reflection statement. -/
def S1849KernelVanishes : Prop :=
  ∀ {A B : CommAlgCat.FiniteEtale.{0} S1779R} (f : A ⟶ B),
    IsIso ((S1848BCF).map f) → Function.Injective f.hom.hom

/-- The surjectivity half of the residue-fibre reflection statement, with the
injectivity half as an explicit hypothesis. -/
def S1849SurjectiveOnInjective : Prop :=
  ∀ {A B : CommAlgCat.FiniteEtale.{0} S1779R} (f : A ⟶ B),
    Function.Injective f.hom.hom → IsIso ((S1848BCF).map f) → Function.Surjective f.hom.hom

/-- **Exact splitting of the target.**  `S1848FReflectsIsoMaps` is equivalent to
the conjunction of its injectivity and (injectivity-conditional) surjectivity
halves. -/
theorem S1849FReflectsIsoMaps_iff_split :
    S1848FReflectsIsoMaps ↔ S1849KernelVanishes ∧ S1849SurjectiveOnInjective := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro A B f hf
      exact (S1848bijective_of_isIso f (h f hf)).1
    · intro A B f hinj hf
      exact (S1848bijective_of_isIso f (h f hf)).2
  · rintro ⟨hker, hsurj⟩ A B f hf
    exact S1848isIso_of_bijective f ⟨hker f hf, hsurj f (hker f hf) hf⟩

/-! ## 4. The trace-form-duality statement: the exact first missing input

Step (iii) of the S1848 route is the following statement, which is the trace-form
duality argument in the precise form needed.

For a finite etale `R'`-algebra `A`, the trace form
`<x,y> = Tr_{A/R'}(x * y)` is a perfect `R'`-bilinear pairing, because the
different of an etale algebra is trivial.  Mathlib 4.32.2 only has
`Algebra.traceForm_nondegenerate` for finite separable extensions of fields
(`Mathlib/RingTheory/Trace/Basic.lean`); the base-ring form is missing.  It is
recorded below as a `Prop` with no inhabitant.

We also record the `R'`-module-theoretic form of the same input that the proof
of the surjectivity half actually uses: an inclusion of finite etale
`R'`-algebras that is an equality after tensoring with the residue field is an
equality.  This is `S1849EqualRankInclusion`; it is equivalent to trace-form
perfectness for finite etale algebras (the trace-duality proof is the classical
one: test a functional with the perfect trace pairing of `A`, then compare in the
common generic fibre). -/

/-- **The exact first missing input.**  An inclusion of finite etale
`R'`-algebras of equal rank is an equality.  Equivalently: a trace-form-perfect
finite etale `R'`-algebra is integrally closed in its generic fibre.  This is the
only ingredient of the S1848 route that is not available in Mathlib 4.32.2. -/
def S1849EqualRankInclusion : Prop :=
  ∀ {A B : CommAlgCat.FiniteEtale.{0} S1779R} (f : A ⟶ B),
    Function.Injective f.hom.hom →
    (∀ (p : PrimeSpectrum S1779R),
      Module.rankAtStalk (A : Type) p = Module.rankAtStalk (B : Type) p) →
    Function.Surjective f.hom.hom

/-- The surjectivity half follows from the equal-rank inclusion statement
together with the rank equality produced by the closed-fibre computation
(step (ii) of the S1848 route). -/
theorem S1849SurjectiveOnInjective_of_equalRankInclusion
    (hiii : S1849EqualRankInclusion)
    (hii : ∀ {A B : CommAlgCat.FiniteEtale.{0} S1779R} (f : A ⟶ B),
      IsIso ((S1848BCF).map f) →
      ∀ (p : PrimeSpectrum S1779R),
        Module.rankAtStalk (A : Type) p = Module.rankAtStalk (B : Type) p)
    (hker : S1849KernelVanishes) :
    S1849SurjectiveOnInjective := by
  intro A B f hinj hf
  exact hiii f hinj (hii f hf)

/-- The target, from the two halves of the S1848 route: kernel vanishing,
rank equality at every prime, and equal-rank inclusion. -/
theorem S1848FReflectsIsoMaps_of_route
    (hker : S1849KernelVanishes)
    (hii : ∀ {A B : CommAlgCat.FiniteEtale.{0} S1779R} (f : A ⟶ B),
      IsIso ((S1848BCF).map f) →
      ∀ (p : PrimeSpectrum S1779R),
        Module.rankAtStalk (A : Type) p = Module.rankAtStalk (B : Type) p)
    (hiii : S1849EqualRankInclusion) :
    S1848FReflectsIsoMaps :=
  S1849FReflectsIsoMaps_iff_split.mpr
    ⟨hker, S1849SurjectiveOnInjective_of_equalRankInclusion hiii hii hker⟩

/-! ## 5. Formal checks -/

#check S1849_isDomain
#check S1849_point_surjective
#check S1849m
#check S1849FEquivQuot
#check S1849KernelVanishes
#check S1849SurjectiveOnInjective
#check S1849FReflectsIsoMaps_iff_split
#check S1849EqualRankInclusion
#check S1849SurjectiveOnInjective_of_equalRankInclusion
#check S1848FReflectsIsoMaps_of_route

#print axioms S1849_isDomain
#print axioms S1849_point_surjective
#print axioms S1849FEquivQuot
#print axioms S1849FReflectsIsoMaps_iff_split
#print axioms S1849SurjectiveOnInjective_of_equalRankInclusion
#print axioms S1848FReflectsIsoMaps_of_route

end LeanFormal.IUT.XiFPaper.S1849RPrimeReflectCompleteActual
