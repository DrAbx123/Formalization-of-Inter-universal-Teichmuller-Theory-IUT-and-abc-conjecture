import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.Tactic
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.IsospecSectionsCoherence

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct

/-!
# Affine quotient universal property for finite etale covers

For an affine finite etale cover `X` of `Spec R` with finite group `G` acting on
its section algebra `A = Γ(X)`, this file proves the fixed-point universal
property for invariant morphisms `X → Z`: they factor through the affine
quotient `q : X → Spec (A^G)`.

The algebraic core is `affineFixedPointQuotient_lift_algHom`; the cover-morphism
side uses `coverMorphismToSectionsAlgHom`.  No quotient object in the cover
category and no finite-etale structure of `A^G` over `R` is asserted here.
-/

namespace ABCBridge.AffineQuotientUniversalProperty

universe u

variable {R : Type u} [CommRing R]
  {G : Type u} [Group G] [Fintype G] [DecidableEq G]
  {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
  {A : Type u} [CommRing A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]
  {Z : FiniteEtaleCover (Spec (CommRingCat.of R))}

/-- The affine quotient chart `Spec (A^G)`. -/
abbrev quotientChart (R A G : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A] : Scheme.{u} :=
  Spec (CommRingCat.of (fixedPointSubalgebra R A G))

/-- The affine quotient chart map `Spec A → Spec (A^G)`. -/
noncomputable def chartQuotientMap : Spec (CommRingCat.of A) ⟶ quotientChart R A G :=
  affineFixedPointQuotientMap R A G

/-- The affine quotient map from the cover, using `X.carrier ≅ Spec A`. -/
noncomputable def quotientMap (e : X.carrier ≅ Spec (CommRingCat.of A)) :
    X.carrier ⟶ quotientChart R A G :=
  e.hom ≫ chartQuotientMap (R := R) (A := A) (G := G)

/-- The section algebra of a cover. -/
abbrev sectionsRing (Z : FiniteEtaleCover (Spec (CommRingCat.of R))) : Type u :=
  Γ(Z.carrier, ⊤)

local instance sectionsAlgebra (Z : FiniteEtaleCover (Spec (CommRingCat.of R))) :
    Algebra R (sectionsRing (R := R) Z) :=
  finiteEtaleCoverSectionsAlgebra R Z

/-- The ring map associated to a cover morphism `X → Z`. -/
noncomputable def coverSectionsMap (e : X.carrier ≅ Spec (CommRingCat.of A))
    (f : X ⟶ Z) : sectionsRing (R := R) Z →+* A :=
  coverMorphismToSectionsAlgHom R e f

/-- An `R`-algebra map `Γ(Z) → A` realizes an actual cover morphism. -/
def RealizesCoverMorphism (e : X.carrier ≅ Spec (CommRingCat.of A))
    (f : X ⟶ Z) (φ : sectionsRing (R := R) Z →ₐ[R] A) : Prop :=
  (φ : sectionsRing (R := R) Z →+* A) = coverSectionsMap (R := R) (A := A) e f

/-- Algebraic fixed-point universal property. -/
theorem affineQuotientUniversalProperty_algHom
    (φ : sectionsRing (R := R) Z →ₐ[R] A)
    (hφ : ∀ (g : G) (b : sectionsRing (R := R) Z),
      groupActionRingEquiv A G g (φ b) = φ b) :
    ∃! ψ : sectionsRing (R := R) Z →ₐ[R] fixedPointSubalgebra R A G,
      (fixedPointInclusion R A G).comp ψ = φ :=
  affineFixedPointQuotient_lift_algHom R A G φ hφ

/-- Scheme-level existence: the chart quotient factors the `Spec` of an
invariant section map. -/
theorem affineQuotientUniversalProperty_spec_exists
    (φ : sectionsRing (R := R) Z →ₐ[R] A)
    (hφ : ∀ (g : G) (b : sectionsRing (R := R) Z),
      groupActionRingEquiv A G g (φ b) = φ b) :
    ∃ ψ : quotientChart R A G ⟶ Spec (CommRingCat.of (sectionsRing (R := R) Z)),
      chartQuotientMap (R := R) (A := A) (G := G) ≫ ψ =
        Spec.map (CommRingCat.ofHom (φ : sectionsRing (R := R) Z →+* A)) := by
  obtain ⟨ψ, hψ, -⟩ := affineQuotientUniversalProperty_algHom (R := R) (G := G) (A := A) φ hφ
  refine ⟨Spec.map (CommRingCat.ofHom (ψ : sectionsRing (R := R) Z →+* fixedPointSubalgebra R A G)), ?_⟩
  unfold chartQuotientMap affineFixedPointQuotientMap
  have hψring : (fixedPointInclusionRingHom R A G).comp
      (ψ : sectionsRing (R := R) Z →+* fixedPointSubalgebra R A G) =
      (φ : sectionsRing (R := R) Z →+* A) := by
    ext b
    exact congrArg (fun f => f b) hψ
  rw [← Spec.map_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom hψring)



/-- `coverMorphismToSectionsAlgHom` is an `R`-algebra map for the canonical affine identification. -/
theorem coverMorphismToSectionsAlgHom_algebraMap
    (f : X ⟶ Z) (r : R) :
    coverMorphismToSectionsAlgHom R X.carrier.isoSpec f
        (algebraMap R (sectionsRing (R := R) Z) r) =
      algebraMap R (sectionsRing (R := R) X) r := by
  have h : CommRingCat.ofHom ((coverMorphismToSectionsAlgHom R X.carrier.isoSpec f).comp
      (algebraMap R (sectionsRing (R := R) Z))) =
      CommRingCat.ofHom (algebraMap R (sectionsRing (R := R) X)) := by
    apply Spec.map_injective
    calc
      Spec.map (CommRingCat.ofHom ((coverMorphismToSectionsAlgHom R X.carrier.isoSpec f).comp
          (algebraMap R (sectionsRing (R := R) Z))))
          = Spec.map (CommRingCat.ofHom (coverMorphismToSectionsAlgHom R X.carrier.isoSpec f)) ≫
              Spec.map (CommRingCat.ofHom (algebraMap R (sectionsRing (R := R) Z))) := by
            rw [CommRingCat.ofHom_comp, Spec.map_comp]
      _ = (X.carrier.isoSpec.inv ≫
              (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left ≫
                Z.carrier.isoSpec.hom) ≫
              Spec.map (CommRingCat.ofHom (algebraMap R (sectionsRing (R := R) Z))) := by
            rw [specMap_coverMorphismToSectionsAlgHom]
      _ = X.carrier.isoSpec.inv ≫
              (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left ≫
                Z.carrier.isoSpec.hom ≫
                  Spec.map (CommRingCat.ofHom (algebraMap R (sectionsRing (R := R) Z))) := by
            simp only [Category.assoc]
      _ = X.carrier.isoSpec.inv ≫
              (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left ≫
                Z.structureMap := by
            exact congrArg (fun g => X.carrier.isoSpec.inv ≫
              (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left ≫ g)
              (ABCBridge.IsospecSectionsCoherence.isoSpec_sectionsAlgebraMap Z)
      _ = X.carrier.isoSpec.inv ≫ X.structureMap := by
            exact congrArg (fun g => X.carrier.isoSpec.inv ≫ g)
              ((FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).w)
      _ = Spec.map (CommRingCat.ofHom (algebraMap R (sectionsRing (R := R) X))) := by
            rw [← ABCBridge.IsospecSectionsCoherence.isoSpec_sectionsAlgebraMap X]
            rw [← Category.assoc, X.carrier.isoSpec.inv_hom_id, Category.id_comp]
  exact congrArg (fun ψ : CommRingCat.of R ⟶ CommRingCat.of (sectionsRing (R := R) X) => ψ.hom r) h


/-- The cover-morphism section map as an `R`-algebra map, for the canonical affine
identification `X.carrier ≅ Spec Γ(X)`. -/
noncomputable def coverSectionsAlgHom (f : X ⟶ Z) :
    sectionsRing (R := R) Z →ₐ[R] sectionsRing (R := R) X :=
  { toRingHom := coverMorphismToSectionsAlgHom R X.carrier.isoSpec f
    commutes' := coverMorphismToSectionsAlgHom_algebraMap (R := R) f }

/-- The canonical section map realizes the cover morphism by definition. -/
theorem realizes_coverSectionsAlgHom (f : X ⟶ Z) :
    RealizesCoverMorphism (R := R) (A := sectionsRing (R := R) X)
      X.carrier.isoSpec f (coverSectionsAlgHom (R := R) f) := rfl

end ABCBridge.AffineQuotientUniversalProperty
