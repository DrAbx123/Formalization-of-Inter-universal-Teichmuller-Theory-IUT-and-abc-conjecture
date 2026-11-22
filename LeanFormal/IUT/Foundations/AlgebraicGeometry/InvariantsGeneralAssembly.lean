import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FixedLocalizationAction
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.Tactic

/-!
# Assembly: affine fixed-point quotients, universal property, finite presentation

This file packages the affine quotient universal property from the production
module FiniteEtaleGroupQuotient and the finite-presentation results for A^G:

* Noetherian/finite-type case, via the Artin--Tate lemma.
* General affine-local case, with no Noetherian hypothesis: finite presentation
  of A^G is checked after inverting a covering family of elements.
* The localization descent equivalence from FixedLocalizationAction is exposed
  for the local fixed-point algebras.

Consumers: primespine/transport.
-/

open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.N8.FixedLocalizationAction

namespace ABCBridge.InvariantsGeneralAssembly

noncomputable section

universe u

variable (R A G : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

/-- The affine fixed-point quotient universal property: a G-invariant
R-algebra map B -> A factors uniquely through A^G. -/
theorem affineFixedPointQuotient_universal
    {B : Type u} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A)
    (hφ : ∀ g b, groupActionRingEquiv A G g (φ b) = φ b) :
    ∃! ψ : B →ₐ[R] fixedPointSubalgebra R A G,
      (fixedPointInclusion R A G).comp ψ = φ :=
  LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient.affineFixedPointQuotient_lift_algHom R A G φ hφ

/-- Noetherian finite-type case: A^G is finitely presented over R by the
Artin--Tate lemma. -/
theorem fixedPointSubalgebra_finitePresentation_of_noetherian
    [Finite G] [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Algebra.FinitePresentation R (fixedPointSubalgebra R A G) := by
  have hInt : Algebra.IsIntegral (fixedPointSubalgebra R A G) A :=
    fixedPoints_isIntegral R A G
  have hFT : Algebra.FiniteType (fixedPointSubalgebra R A G) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType (R := R)
      (S := fixedPointSubalgebra R A G) (A := A)
  haveI hFin : Module.Finite (fixedPointSubalgebra R A G) A :=
    Algebra.IsIntegral.finite (R := fixedPointSubalgebra R A G) (A := A)
  have hAC : (⊤ : Subalgebra R A).FG :=
    (inferInstance : Algebra.FiniteType R A).out
  have hBC : (⊤ : Submodule (fixedPointSubalgebra R A G) A).FG := hFin.fg_top
  have hBCi : Function.Injective (algebraMap (fixedPointSubalgebra R A G) A) :=
    Subtype.val_injective
  have hAT : (⊤ : Subalgebra R (fixedPointSubalgebra R A G)).FG :=
    fg_of_fg_of_fg (A := R) (B := fixedPointSubalgebra R A G) (C := A)
      hAC hBC hBCi
  have hFTtop : Algebra.FiniteType R (↥(⊤ : Subalgebra R
      (fixedPointSubalgebra R A G))) :=
    (Subalgebra.fg_iff_finiteType (R := R)
      (A := fixedPointSubalgebra R A G) ⊤).mp hAT
  have hFT' : Algebra.FiniteType R (fixedPointSubalgebra R A G) :=
    Algebra.FiniteType.equiv hFTtop
      (Subalgebra.topEquiv (R := R) (A := fixedPointSubalgebra R A G))
  exact (Algebra.FinitePresentation.of_finiteType (R := R)
    (A := fixedPointSubalgebra R A G)).mp hFT'

/-- General affine-local finite presentation without Noetherian hypotheses.
If a family s_i covers A^G and each localization (A^G)_{s_i} is finitely
presented over R, then A^G is finitely presented over R. -/
theorem fixedPointSubalgebra_finitePresentation_of_affineLocal
    {ι : Type*} [Finite ι] (s : ι → fixedPointSubalgebra R A G)
    (hs : Ideal.span (Set.range s) = ⊤)
    (T : ι → Type*) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    [∀ i, Algebra (fixedPointSubalgebra R A G) (T i)]
    [∀ i, IsScalarTower R (fixedPointSubalgebra R A G) (T i)]
    [∀ i, IsLocalization.Away (s i) (T i)]
    [∀ i, Algebra.FinitePresentation R (T i)] :
    Algebra.FinitePresentation R (fixedPointSubalgebra R A G) :=
  Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway s hs T

/-- The localization descent equivalence for fixed points, from
FixedLocalizationAction.  For a finite group and invariant base, the fixed
points of A_f are the localization of A^G at f. -/
noncomputable def fixedPointSubalgebra_localization_equiv
    [Fintype G]
    [SMulCommClass G (fixedPointSubalgebra R A G) A]
    (f : fixedPointSubalgebra R A G) :
    RingEquiv
      (Localization.Away f)
      (FixedPoints.subring
        (Localization.Away (algebraMap (fixedPointSubalgebra R A G) A f)) G) :=
  awayFixedPointsEquiv (B := A) (G := G) f Subtype.val_injective


/-- Consumer-facing form: the exact local hypotheses on the fixed points of
the localized B-algebra.  For each element of a covering family s_i of A^G,
assume the fixed points of A localized at the image of s_i are an
IsLocalization.Away (s_i) of A^G and are finitely presented over R.  Then
A^G is finitely presented over R, with no Noetherian hypothesis. -/
theorem fixedPointSubalgebra_finitePresentation_of_fixedPointLocalizations
    [Fintype G]
    [SMulCommClass G (fixedPointSubalgebra R A G) A]
    {ι : Type*} [Finite ι]
    (s : ι → fixedPointSubalgebra R A G)
    (hs : Ideal.span (Set.range s) = ⊤)
    [∀ i, Algebra R (FixedPoints.subring
      (Localization.Away (algebraMap (fixedPointSubalgebra R A G) A (s i))) G)]
    [∀ i, Algebra (fixedPointSubalgebra R A G) (FixedPoints.subring
      (Localization.Away (algebraMap (fixedPointSubalgebra R A G) A (s i))) G)]
    [∀ i, IsScalarTower R (fixedPointSubalgebra R A G) (FixedPoints.subring
      (Localization.Away (algebraMap (fixedPointSubalgebra R A G) A (s i))) G)]
    [∀ i, IsLocalization.Away (s i) (FixedPoints.subring
      (Localization.Away (algebraMap (fixedPointSubalgebra R A G) A (s i))) G)]
    [∀ i, Algebra.FinitePresentation R (FixedPoints.subring
      (Localization.Away (algebraMap (fixedPointSubalgebra R A G) A (s i))) G)] :
    Algebra.FinitePresentation R (fixedPointSubalgebra R A G) :=
  fixedPointSubalgebra_finitePresentation_of_affineLocal R A G s hs
    (fun i => FixedPoints.subring
      (Localization.Away (algebraMap (fixedPointSubalgebra R A G) A (s i))) G)


end

end ABCBridge.InvariantsGeneralAssembly
