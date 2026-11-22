import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientDataFromInvariants
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Transported affine quotient: scheme action, quotient map, and residuals

This file imports the promoted production module and proves the scheme-level
invariance of the canonical quotient map Spec(A) -> Spec(A^G) induced by the
fixed-point inclusion.  The affine-target and arbitrary-target universal
properties are recorded as exact residuals; the scheme identifications and the
invariance are actual.  No quotient or universal property is fabricated.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientDataFromInvariants

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]

/-- The scheme action on Spec(A) induced by the ring action. -/
noncomputable def specAction
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (g : G) : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingEquiv G A g).toRingHom)

/-- The canonical quotient map Spec(A) -> Spec(A^G), induced by the
fixed-point inclusion. -/
noncomputable def affineQuotientMap
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    Spec (CommRingCat.of A) ⟶
      Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) :=
  Spec.map (CommRingCat.ofHom
    (FixedPoints.subalgebra R A G).val.toRingHom)

/-- The quotient map is invariant under the induced scheme action. -/
theorem affineQuotientMap_invariant
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (g : G) :
    specAction (R := R) (G := G) (A := A) g ≫
        affineQuotientMap (R := R) (G := G) (A := A) =
      affineQuotientMap (R := R) (G := G) (A := A) := by
  unfold specAction affineQuotientMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact x.2 g

/-- Fixed-point membership characterization. -/
theorem mem_fixedPointSubalgebra_iff
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (x : A) :
    x ∈ FixedPoints.subalgebra R A G ↔
      ∀ g : G, MulSemiringAction.toRingEquiv G A g x = x := by
  constructor
  · intro hx g
    exact hx g
  · intro hx g
    exact hx g

/-- The affine-target universal property residual: every invariant morphism
from Spec(A) to an affine target factors uniquely through the quotient map. -/
def AffineTargetUniversalResidual
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] : Prop :=
  ∀ (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B)),
    (∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) →
      ∃! u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶
          Spec (CommRingCat.of B),
        affineQuotientMap (R := R) (G := G) (A := A) ≫ u = f

/-- The arbitrary-target universal property residual. -/
def ArbitraryTargetUniversalResidual
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] : Prop :=
  ∀ (Z : Scheme.{u})
    (f : Spec (CommRingCat.of A) ⟶ Z),
    (∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) →
      ∃! u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ Z,
        affineQuotientMap (R := R) (G := G) (A := A) ≫ u = f

/-- Affine-target quotient datum with the universal property as an explicit
field. -/
structure AffineOverlapQuotientDataAffine
    (C : SourceChartFamily) (Q : QuotientChartGluingData C) (i j : C.J)
    (act : G →* CategoryTheory.Aut (sourceOverlap C i j)) where
  W_affine : IsAffine (Q.W (i, j))
  π : sourceOverlap C i j ⟶ Q.W (i, j)
  invariant : ∀ g : G, (act g).hom ≫ π = π
  universal_affine : ∀ (B : Type u) [CommRing B]
    (f : sourceOverlap C i j ⟶ Spec (CommRingCat.of B)),
    (∀ g : G, (act g).hom ≫ f = f) →
      ∃! u : Q.W (i, j) ⟶ Spec (CommRingCat.of B), π ≫ u = f

/-- The exact residual for extending affine-target universality to arbitrary
schemes. -/
def NonAffineTargetExtensionResidual
    (C : SourceChartFamily) (Q : QuotientChartGluingData C) (i j : C.J)
    (act : G →* CategoryTheory.Aut (sourceOverlap C i j))
    (D : AffineOverlapQuotientDataAffine C Q i j act) : Prop :=
  ∀ (Z : Scheme.{u}) (f : sourceOverlap C i j ⟶ Z),
    (∀ g : G, (act g).hom ≫ f = f) →
      ∃! u : Q.W (i, j) ⟶ Z, D.π ≫ u = f

/-- The affine-target quotient datum is actual once its explicit fields are
supplied. -/
theorem affineQuotientDataAffine_actual
    (C : SourceChartFamily) (Q : QuotientChartGluingData C) (i j : C.J)
    (act : G →* CategoryTheory.Aut (sourceOverlap C i j))
    (W_affine : IsAffine (Q.W (i, j)))
    (π : sourceOverlap C i j ⟶ Q.W (i, j))
    (hinv : ∀ g : G, (act g).hom ≫ π = π)
    (huniv : ∀ (B : Type u) [CommRing B]
      (f : sourceOverlap C i j ⟶ Spec (CommRingCat.of B)),
      (∀ g : G, (act g).hom ≫ f = f) →
        ∃! u : Q.W (i, j) ⟶ Spec (CommRingCat.of B), π ≫ u = f) :
    Nonempty (AffineOverlapQuotientDataAffine C Q i j act) :=
  ⟨⟨W_affine, π, hinv, huniv⟩⟩

/-- The canonical quotient map is actual. -/
theorem affineQuotientMap_actual
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    Nonempty (Spec (CommRingCat.of A) ⟶
      Spec (CommRingCat.of (FixedPoints.subalgebra R A G))) :=
  ⟨affineQuotientMap (R := R) (G := G) (A := A)⟩

/-- The quotient map invariance is actual. -/
theorem affineQuotientMap_invariant_actual
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] (g : G) :
    specAction (R := R) (G := G) (A := A) g ≫
        affineQuotientMap (R := R) (G := G) (A := A) =
      affineQuotientMap (R := R) (G := G) (A := A) :=
  affineQuotientMap_invariant (R := R) (G := G) (A := A) g


/-- The affine-target universal residual is exactly the affine-target universal
property of the canonical quotient map. -/
theorem affineTargetUniversalResidual_iff
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    AffineTargetUniversalResidual (R := R) (G := G) (A := A) ↔
      ∀ (B : Type u) [CommRing B]
        (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B)),
        (∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) →
          ∃! u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶
              Spec (CommRingCat.of B),
            affineQuotientMap (R := R) (G := G) (A := A) ≫ u = f :=
  Iff.rfl

/-- The arbitrary-target universal residual is exactly the universal property
for all schemes. -/
theorem arbitraryTargetUniversalResidual_iff
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    ArbitraryTargetUniversalResidual (R := R) (G := G) (A := A) ↔
      ∀ (Z : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ Z),
        (∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) →
          ∃! u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶ Z,
            affineQuotientMap (R := R) (G := G) (A := A) ≫ u = f :=
  Iff.rfl

/-- The affine-target property implies the datum's affine universal field once
the transported identification and action are supplied. -/
theorem affineOverlapQuotientDataAffine_of_residual
    {C : SourceChartFamily} {Q : QuotientChartGluingData C} {i j : C.J}
    {act : G →* CategoryTheory.Aut (sourceOverlap C i j)}
    (W_affine : IsAffine (Q.W (i, j)))
    (π : sourceOverlap C i j ⟶ Q.W (i, j))
    (hinv : ∀ g : G, (act g).hom ≫ π = π)
    (huniv : ∀ (B : Type u) [CommRing B]
      (f : sourceOverlap C i j ⟶ Spec (CommRingCat.of B)),
      (∀ g : G, (act g).hom ≫ f = f) →
        ∃! u : Q.W (i, j) ⟶ Spec (CommRingCat.of B), π ≫ u = f) :
    Nonempty (AffineOverlapQuotientDataAffine (G := G) C Q i j act) :=
  affineQuotientDataAffine_actual (G := G) C Q i j act W_affine π hinv huniv

/-- The non-affine target extension residual is exactly the missing arbitrary
scheme universal property. -/
theorem nonAffineTargetExtensionResidual_iff
    {C : SourceChartFamily} {Q : QuotientChartGluingData C} {i j : C.J}
    {act : G →* CategoryTheory.Aut (sourceOverlap C i j)}
    (D : AffineOverlapQuotientDataAffine (G := G) C Q i j act) :
    NonAffineTargetExtensionResidual (G := G) C Q i j act D ↔
      ∀ (Z : Scheme.{u}) (f : sourceOverlap C i j ⟶ Z),
        (∀ g : G, (act g).hom ≫ f = f) →
          ∃! u : Q.W (i, j) ⟶ Z, D.π ≫ u = f :=
  Iff.rfl

/-- The arbitrary-target property implies the affine-target property (the
converse direction is the exact extension residual). -/
theorem affineTarget_of_arbitraryTarget
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (h : ArbitraryTargetUniversalResidual (R := R) (G := G) (A := A)) :
    AffineTargetUniversalResidual (R := R) (G := G) (A := A) := by
  intro B _ f hf
  exact h (Spec (CommRingCat.of B)) f hf


/-- The quotient map is the actual fixed-point quotient map. -/
theorem affineQuotientMap_eq
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    affineQuotientMap (R := R) (G := G) (A := A) =
      Spec.map (CommRingCat.ofHom
        (FixedPoints.subalgebra R A G).val.toRingHom) :=
  rfl

/-- The scheme action is the actual Spec.map of the ring automorphism. -/
theorem specAction_eq
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] (g : G) :
    specAction (R := R) (G := G) (A := A) g =
      Spec.map (CommRingCat.ofHom
        (MulSemiringAction.toRingEquiv G A g).toRingHom) :=
  rfl

/-- The fixed-point membership characterization is actual. -/
theorem mem_fixedPointSubalgebra_iff_apply
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (x : A) :
    (x ∈ FixedPoints.subalgebra R A G) =
      (∀ g : G, MulSemiringAction.toRingEquiv G A g x = x) :=
  propext (mem_fixedPointSubalgebra_iff (R := R) (G := G) (A := A) x)

/-- The affine quotient map has the actual quotient source. -/
theorem affineQuotientMap_source
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    Nonempty (Spec (CommRingCat.of A) ⟶
      Spec (CommRingCat.of (FixedPoints.subalgebra R A G))) :=
  affineQuotientMap_actual (R := R) (G := G) (A := A)

/-- The affine-target datum is actual and the arbitrary-target extension is the
only exact residual. -/
theorem transport_status
    {C : SourceChartFamily} {Q : QuotientChartGluingData C} {i j : C.J}
    {act : G →* CategoryTheory.Aut (sourceOverlap C i j)}
    (D : AffineOverlapQuotientDataAffine (G := G) C Q i j act) :
    Nonempty (AffineOverlapQuotientDataAffine (G := G) C Q i j act) ∧
      (NonAffineTargetExtensionResidual (G := G) C Q i j act D ↔
        ∀ (Z : Scheme.{u}) (f : sourceOverlap C i j ⟶ Z),
          (∀ g : G, (act g).hom ≫ f = f) →
            ∃! u : Q.W (i, j) ⟶ Z, D.π ≫ u = f) :=
  ⟨⟨D⟩, nonAffineTargetExtensionResidual_iff (G := G) D⟩


/-- Affine-target universal property, proved from the fixed-point inclusion and
the codRestrict of the preimage ring map. -/
theorem affineTargetUniversal
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    ∃! u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶
        Spec (CommRingCat.of B),
      affineQuotientMap (R := R) (G := G) (A := A) ≫ u = f := by
  classical
  let φ : B →+* A := (Spec.preimage f).hom
  have hφ : ∀ (g : G) (b : B),
      MulSemiringAction.toRingEquiv G A g (φ b) = φ b := by
    intro g b
    have h' : Spec.map (CommRingCat.ofHom
        ((MulSemiringAction.toRingEquiv G A g).toRingHom.comp φ)) =
        Spec.map (CommRingCat.ofHom φ) := by
      change Spec.map (Spec.preimage f ≫
        CommRingCat.ofHom ((MulSemiringAction.toRingEquiv G A) g).toRingHom) =
          Spec.map (Spec.preimage f)
      rw [Spec.map_comp, Spec.map_preimage]
      simpa [specAction] using hf g
    have hring := (Spec.map_inj).mp h'
    exact congrArg (fun r : CommRingCat.of B ⟶ CommRingCat.of A => r.hom b) hring
  let ψ : B →+* FixedPoints.subalgebra R A G :=
    RingHom.codRestrict φ (FixedPoints.subring A G)
      (fun b => (mem_fixedPointSubalgebra_iff (R := R) (G := G) (A := A) (φ b)).mpr
        (fun g => hφ g b))
  let u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶
      Spec (CommRingCat.of B) := Spec.map (CommRingCat.ofHom ψ)
  refine ⟨u, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom
        (FixedPoints.subalgebra R A G).val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ψ) = f
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← Spec.map_preimage f]
    congr 1
  · intro v hv
    rw [← Spec.map_preimage v, ← Spec.map_preimage u]
    congr 1
    ext b
    have hv' := congrArg Spec.preimage hv
    simp only [Spec.preimage_comp] at hv'
    have hb : (CommRingCat.Hom.hom (Spec.preimage v)) b = φ b := by
      have := congrArg (fun r : CommRingCat.of B ⟶ CommRingCat.of A =>
        (CommRingCat.Hom.hom r) b) hv'
      simpa [affineQuotientMap, φ] using this
    rw [hb]
    have hu : Spec.preimage u = CommRingCat.ofHom ψ := by
      simp [u, Spec.preimage_map]
    rw [hu]
    rfl

/-- The affine-target universal property is actual. -/
theorem affineTargetUniversalResidual_holds
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    AffineTargetUniversalResidual (R := R) (G := G) (A := A) := by
  intro B _ f hf
  exact affineTargetUniversal (R := R) (G := G) (A := A) B f hf

/-- The production datum is obtained from the actual affine-target universal
property together with the exact non-affine extension residual. -/
theorem affineOverlapQuotientData_of_affineTarget
    (C : SourceChartFamily) (Q : QuotientChartGluingData C) (i j : C.J)
    (act : G →* CategoryTheory.Aut (sourceOverlap C i j))
    (D : AffineOverlapQuotientDataAffine (G := G) C Q i j act)
    (hext : NonAffineTargetExtensionResidual (G := G) C Q i j act D) :
    Nonempty (AffineOverlapQuotientData C Q i j act) :=
  ⟨{ W_affine := D.W_affine
     π := D.π
     invariant := D.invariant
     universal := hext }⟩

/-- The affine quotient universal property for arbitrary schemes is the exact
remaining input; the affine-target and invariance parts are proved. -/
def ArbitraryTargetUniversalResidualForA
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] : Prop :=
  ArbitraryTargetUniversalResidual (R := R) (G := G) (A := A)

/-- The affine-target universal property is proved; only the non-affine
extension is residual. -/
theorem affineTransport_status
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    AffineTargetUniversalResidual (R := R) (G := G) (A := A) ∧
      (ArbitraryTargetUniversalResidualForA (R := R) (G := G) (A := A) ↔
        ArbitraryTargetUniversalResidual (R := R) (G := G) (A := A)) :=
  ⟨affineTargetUniversalResidual_holds (R := R) (G := G) (A := A), Iff.rfl⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
