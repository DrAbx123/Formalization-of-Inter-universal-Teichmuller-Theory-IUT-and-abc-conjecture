import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic

/-!
# Affine fixed-point quotients by finite groups

This file begins the actual construction of the quotient of a finite etale cover by a
finite group action in the affine case.  For an affine finite etale map Spec A -> Spec R
with an action of a finite group G by R-algebra automorphisms, the fixed-point subalgebra
A^G is defined, together with the canonical affine quotient map Spec A -> Spec A^G, its
G-invariance, the fixed-point universal property for algebra maps (the affine quotient
property), and the integrality of A over A^G.

Scoped status: this is the affine fixed-point layer only.  The finite-etale structure of
A^G over R and the affine-local gluing/descent to a general finite etale cover are not
proved here; no card or placeholder is introduced for them.
-/
open AlgebraicGeometry CategoryTheory

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
noncomputable section
universe u
variable (R A G : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

def fixedPointSubalgebra : Subalgebra R A := FixedPoints.subalgebra R A G

def fixedPointInclusion : fixedPointSubalgebra R A G →ₐ[R] A := (fixedPointSubalgebra R A G).val

def fixedPointInclusionRingHom : fixedPointSubalgebra R A G →+* A :=
  (fixedPointInclusion R A G).toRingHom

def affineFixedPointQuotientMap :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of ↥(fixedPointSubalgebra R A G)) :=
  Spec.map (CommRingCat.ofHom (fixedPointInclusionRingHom R A G))


theorem fixedPointInclusion_comp_algebraMap :
    (fixedPointInclusionRingHom R A G).comp
        (algebraMap R (fixedPointSubalgebra R A G)) =
      algebraMap R A := by
  ext r
  exact (fixedPointInclusion R A G).commutes r

theorem affineFixedPointQuotientMap_comp_specMap_algebraMap :
    affineFixedPointQuotientMap R A G ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (fixedPointSubalgebra R A G))) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  unfold affineFixedPointQuotientMap
  rw [← Spec.map_comp]
  refine congrArg Spec.map ?_
  rw [← CommRingCat.ofHom_comp]
  exact congrArg CommRingCat.ofHom (fixedPointInclusion_comp_algebraMap R A G)

theorem fixedPointInclusion_smul (g : G) (x : fixedPointSubalgebra R A G) :
    g • (fixedPointInclusion R A G x : A) = fixedPointInclusion R A G x := x.2 g

def groupActionRingEquiv (g : G) : A ≃+* A := MulSemiringAction.toRingEquiv G A g

def groupActionSpecAut (g : G) : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (groupActionRingEquiv A G g : A →+* A))

theorem groupActionSpecAut_comp_affineFixedPointQuotientMap (g : G) :
    groupActionSpecAut A G g ≫ affineFixedPointQuotientMap R A G =
      affineFixedPointQuotientMap R A G := by
  unfold groupActionSpecAut affineFixedPointQuotientMap
  rw [← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp]
  congr 1
  ext x
  simpa [groupActionRingEquiv, fixedPointInclusionRingHom] using
    fixedPointInclusion_smul R A G g x

instance fixedPoints_isInvariant : Algebra.IsInvariant (fixedPointSubalgebra R A G) A G :=
  ⟨fun x hx => ⟨⟨x, fun g => hx g⟩, rfl⟩⟩

theorem fixedPoints_isIntegral [Finite G] :
    Algebra.IsIntegral (fixedPointSubalgebra R A G) A :=
  Algebra.IsInvariant.isIntegral (fixedPointSubalgebra R A G) A G



theorem fixedPoints_isIntegral_over_base [Module.Finite R A] :
    Algebra.IsIntegral R (fixedPointSubalgebra R A G) :=
  Algebra.IsIntegral.of_injective (fixedPointSubalgebra R A G).val Subtype.val_injective

theorem fixedPoints_finiteType_over_self [Module.Finite R A] :
    Algebra.FiniteType (fixedPointSubalgebra R A G) A :=
  Algebra.FiniteType.of_restrictScalars_finiteType (R := R)
    (S := fixedPointSubalgebra R A G) (A := A)

theorem fixedPoints_finite_over_self [Finite G] [Module.Finite R A] :
    Module.Finite (fixedPointSubalgebra R A G) A := by
  haveI := fixedPoints_isIntegral R A G
  haveI := fixedPoints_finiteType_over_self R A G
  exact Algebra.IsIntegral.finite

theorem fixedPoints_formallyUnramified_over_self [Algebra.Etale R A] :
    Algebra.FormallyUnramified (fixedPointSubalgebra R A G) A :=
  Algebra.FormallyUnramified.of_restrictScalars R (fixedPointSubalgebra R A G) A

theorem fixedPoints_etale_iff [Module.Finite R A] :
    Algebra.Etale R (fixedPointSubalgebra R A G) ↔
      Module.Flat R (fixedPointSubalgebra R A G) ∧
        Algebra.FormallyUnramified R (fixedPointSubalgebra R A G) ∧
          Algebra.FinitePresentation R (fixedPointSubalgebra R A G) := by
  rw [← RingHom.etale_algebraMap, RingHom.Etale.iff_flat_and_formallyUnramified,
    RingHom.flat_algebraMap_iff, RingHom.formallyUnramified_algebraMap,
    RingHom.finitePresentation_algebraMap]

theorem fixedPoints_moduleFinite_of_etale [Module.Finite R A]
    (h : Algebra.Etale R (fixedPointSubalgebra R A G)) :
    Module.Finite R (fixedPointSubalgebra R A G) := by
  haveI := fixedPoints_isIntegral_over_base R A G
  exact Algebra.IsIntegral.finite


theorem fixedPointInclusionRingHom_finite [Finite G] [Module.Finite R A] :
    (fixedPointInclusionRingHom R A G).Finite := by
  change (algebraMap (fixedPointSubalgebra R A G) A).Finite
  rw [RingHom.finite_algebraMap]
  letI : Algebra.FiniteType R A := Module.Finite.finiteType A
  letI : Algebra.FiniteType (fixedPointSubalgebra R A G) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType (R := R)
      (S := fixedPointSubalgebra R A G) (A := A)
  letI : Algebra.IsIntegral (fixedPointSubalgebra R A G) A := fixedPoints_isIntegral R A G
  exact Algebra.IsIntegral.finite

theorem affineFixedPointQuotientMap_isFinite [Finite G] [Module.Finite R A] :
    IsFinite (affineFixedPointQuotientMap R A G) := by
  rw [affineFixedPointQuotientMap]
  exact (AlgebraicGeometry.IsFinite.SpecMap_iff
    (f := CommRingCat.ofHom (fixedPointInclusionRingHom R A G))).mpr
    (fixedPointInclusionRingHom_finite R A G)

theorem affineFixedPointQuotient_lift_algHom
    {B : Type u} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A)
    (hφ : ∀ g b, groupActionRingEquiv A G g (φ b) = φ b) :
    ∃! ψ : B →ₐ[R] fixedPointSubalgebra R A G,
      (fixedPointInclusion R A G).comp ψ = φ := by
  let ψ : B →ₐ[R] fixedPointSubalgebra R A G :=
    φ.codRestrict (fixedPointSubalgebra R A G) fun b => by
      change ∀ g : G, g • φ b = φ b
      intro g
      simpa [groupActionRingEquiv] using hφ g b
  refine ⟨ψ, ?_, ?_⟩
  · ext b
    rfl
  · intro ψ' hψ'
    ext b
    have h := congrArg (fun f => f b) hψ'
    simpa [fixedPointInclusion, ψ] using h

end
end LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient