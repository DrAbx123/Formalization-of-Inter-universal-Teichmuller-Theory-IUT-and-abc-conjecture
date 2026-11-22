import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CoverSectionsAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace SHEAF.L03.UniversalBundled

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [Finite G]
variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
variable {A : Type u} [CommRing A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]
variable (e : X.carrier ≅ Spec (CommRingCat.of A))

/-- Quotient map from the cover carrier to the fixed-point chart. -/
noncomputable def quotientProjection :
    X.carrier ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) :=
  e.hom ≫ affineQuotientProjection (R := R) (G := G) (A := A)


/-- Underlying scheme automorphism of a cover action. -/
noncomputable def actLeft (act : G →* CategoryTheory.Aut X) (g : G) :
    X.carrier ⟶ X.carrier :=
  (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map (act g).hom).left

/-- Compatibility of a cover action with the given algebra action. -/
def ActionCompatible (e : X.carrier ≅ Spec (CommRingCat.of A))
    (act : G →* CategoryTheory.Aut X) : Prop :=
  ∀ g : G, e.hom ≫ specAction (R := R) (G := G) (A := A) g =
    actLeft act g ≫ e.hom

/-- The quotient map is invariant under a compatible cover action. -/
theorem pi_invariant (act : G →* CategoryTheory.Aut X)
    (hact : ActionCompatible e act) (g : G) :
    actLeft act g ≫ (e.hom ≫ affineQuotientProjection (R := R) (G := G) (A := A)) =
      e.hom ≫ affineQuotientProjection (R := R) (G := G) (A := A) := by
  rw [← Category.assoc, ← hact g, Category.assoc]
  exact congrArg (fun u => e.hom ≫ u)
    (affineQuotientProjection_invariant (R := R) (G := G) (A := A) (g := g))

/-- Underlying scheme map of a cover morphism. -/
noncomputable def coverLeft {Z : FiniteEtaleCover (Spec (CommRingCat.of R))} (f : X ⟶ Z) :
    X.carrier ⟶ Z.carrier :=
  (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left

/-- The affine map associated with a cover morphism. -/
noncomputable def targetAffine {B : Type u} [CommRing B]
    {Z : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (eB : Z.carrier ≅ Spec (CommRingCat.of B)) (f : X ⟶ Z) :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B) :=
  e.inv ≫ coverLeft f ≫ eB.hom

/-- Invariance of the affine target map. -/
theorem targetAffine_invariant (act : G →* CategoryTheory.Aut X)
    (hact : ActionCompatible e act)
    {B : Type u} [CommRing B] {Z : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (eB : Z.carrier ≅ Spec (CommRingCat.of B))
    (f : X ⟶ Z) (hf : ∀ g : G, actLeft act g ≫ coverLeft f = coverLeft f) (g : G) :
    specAction (R := R) (G := G) (A := A) g ≫ targetAffine e eB f =
      targetAffine e eB f := by
  unfold targetAffine
  have hcomp : specAction (R := R) (G := G) (A := A) g ≫ e.inv =
      e.inv ≫ actLeft act g := by
    calc
      specAction (R := R) (G := G) (A := A) g ≫ e.inv
          = (e.inv ≫ e.hom) ≫ specAction (R := R) (G := G) (A := A) g ≫ e.inv := by
              rw [Iso.inv_hom_id, Category.id_comp]
      _ = e.inv ≫ (e.hom ≫ specAction (R := R) (G := G) (A := A) g) ≫ e.inv := by
              simp only [Category.assoc]
      _ = e.inv ≫ (actLeft act g ≫ e.hom) ≫ e.inv := by rw [hact g]
      _ = e.inv ≫ actLeft act g := by
              simp only [Category.assoc]
              rw [Iso.hom_inv_id, Category.comp_id]
  change (specAction (R := R) (G := G) (A := A) g ≫ e.inv) ≫ coverLeft f ≫ eB.hom =
    e.inv ≫ coverLeft f ≫ eB.hom
  rw [hcomp]
  simpa only [Category.assoc] using
    congrArg (fun u => e.inv ≫ u ≫ eB.hom) (hf g)

/-- Universal property for G-invariant cover morphisms. -/
theorem universal {Z : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (act : G →* CategoryTheory.Aut X)
    (hact : ActionCompatible e act)
    {B : Type u} [CommRing B] (eB : Z.carrier ≅ Spec (CommRingCat.of B))
    (f : X ⟶ Z) (hf : ∀ g : G, actLeft act g ≫ coverLeft f = coverLeft f) :
    ∃! u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ Z.carrier,
      (e.hom ≫ affineQuotientProjection (R := R) (G := G) (A := A)) ≫ u = coverLeft f := by
  let target := targetAffine e eB f
  have htarget : ∀ g : G,
      specAction (R := R) (G := G) (A := A) g ≫ target = target :=
    targetAffine_invariant e act hact eB f hf
  obtain ⟨u, hu, huniq⟩ :=
    affineQuotientUniversal A B target htarget
  refine ⟨u ≫ eB.inv, ?_, ?_⟩
  · calc
      (e.hom ≫ affineQuotientProjection (R := R) (G := G) (A := A)) ≫ (u ≫ eB.inv)
          = e.hom ≫ (affineQuotientProjection (R := R) (G := G) (A := A) ≫ u) ≫ eB.inv := by
              simp only [Category.assoc]
      _ = e.hom ≫ target ≫ eB.inv := by rw [hu]
      _ = coverLeft f := by
              unfold target targetAffine
              simp only [Category.assoc]
              rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  · intro v hv
    have hv' : affineQuotientProjection (R := R) (G := G) (A := A) ≫
        (v ≫ eB.hom) = target := by
      unfold target targetAffine
      rw [← hv]
      simp only [Category.assoc]
      rw [Iso.inv_hom_id_assoc]
    have hvu := huniq (v ≫ eB.hom) hv'
    rw [← hvu]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id, Category.comp_id]

end SHEAF.L03.UniversalBundled
