import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Ring.Action.Submonoid

/-!
# Affine overlap quotient from the invariant algebra

For an affine chart overlap with coordinate ring A and a finite group action,
the affine quotient is Spec(A^G), with quotient map induced by the fixed-point
inclusion.  This file constructs that map and transports it along actual affine
identifications.  The group action on the overlap is explicit actual data; the
algebra quotient is Spec(A^G).  The transported invariance and universal
property are explicit input, not fabricated.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientDataFromInvariants

universe u

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]

/-- Minimal source chart family for an affine overlap. -/
structure SourceChartFamily where
  J : Type u
  X : Scheme.{u}
  U : J → Scheme.{u}
  chartι : ∀ i : J, U i ⟶ X
  chart_open : ∀ i, IsOpenImmersion (chartι i)
  chart_cover : ∀ x : X, ∃ (i : J) (y : U i), chartι i y = x
  chart_affine : ∀ i, IsAffine (U i)
  hasPullback : ∀ i j, HasPullback (chartι i) (chartι j)

/-- The source chart overlap. -/
noncomputable def sourceOverlap (C : SourceChartFamily) (i j : C.J) : Scheme.{u} := by
  letI := C.hasPullback i j
  exact pullback (C.chartι i) (C.chartι j)

/-- Minimal quotient gluing data for the quotient chart overlap. -/
structure QuotientChartGluingData (C : SourceChartFamily) where
  Q : Scheme.{u}
  W : C.J × C.J → Scheme.{u}

/-- The affine quotient datum of a source chart overlap, for an actual group
action on the overlap. -/
structure AffineOverlapQuotientData
    (C : SourceChartFamily) (Q : QuotientChartGluingData C) (i j : C.J)
    (act : G →* CategoryTheory.Aut (sourceOverlap C i j)) where
  W_affine : IsAffine (Q.W (i, j))
  π : sourceOverlap C i j ⟶ Q.W (i, j)
  invariant : ∀ g : G, (act g).hom ≫ π = π
  universal : ∀ (Z : Scheme.{u}) (f : sourceOverlap C i j ⟶ Z),
    (∀ g : G, (act g).hom ≫ f = f) →
      ∃! u : Q.W (i, j) ⟶ Z, π ≫ u = f

/-- Affine coordinate data for a source chart overlap. -/
structure AffineOverlapCoordinateData
    (C : SourceChartFamily) (Q : QuotientChartGluingData C) (i j : C.J)
    (act : G →* CategoryTheory.Aut (sourceOverlap C i j)) where
  A : Type u
  [commRing : CommRing A]
  [algebra : Algebra R A]
  [action : MulSemiringAction G A]
  [smulComm : SMulCommClass G R A]
  W_affine : IsAffine (Q.W (i, j))
  overlapIso : sourceOverlap C i j ≅ Spec (CommRingCat.of A)
  quotientIso : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ≅ Q.W (i, j)

attribute [instance] AffineOverlapCoordinateData.commRing
attribute [instance] AffineOverlapCoordinateData.algebra
attribute [instance] AffineOverlapCoordinateData.action
attribute [instance] AffineOverlapCoordinateData.smulComm

namespace AffineOverlapCoordinateData

variable {C : SourceChartFamily}
variable {Q : QuotientChartGluingData C}
variable {i j : C.J}
variable {act : G →* CategoryTheory.Aut (sourceOverlap C i j)}
  (D : AffineOverlapCoordinateData (R := R) (G := G) C Q i j act)

/-- The algebra fixed-point inclusion A^G → A. -/
noncomputable def quotientAlgebraMap :
    FixedPoints.subalgebra R D.A G →+* D.A :=
  Subalgebra.val (FixedPoints.subalgebra R D.A G)

/-- The affine quotient map from Spec(A) to Spec(A^G), induced by the
fixed-point inclusion. -/
noncomputable def affineQuotientMap :
    Spec (CommRingCat.of D.A) ⟶
      Spec (CommRingCat.of (FixedPoints.subalgebra R D.A G)) :=
  Spec.map (CommRingCat.ofHom (quotientAlgebraMap D))

/-- The transported quotient map from the source overlap to the quotient chart
overlap. -/
noncomputable def quotientMap : sourceOverlap C i j ⟶ Q.W (i, j) :=
  D.overlapIso.hom ≫ affineQuotientMap D ≫ D.quotientIso.hom

/-- The actual affine overlap quotient datum, conditional on the transported
invariance and universal property. -/
noncomputable def toAffineOverlapQuotientData
    (hinv : ∀ g : G, (act g).hom ≫ quotientMap D = quotientMap D)
    (huniv : ∀ (Z : Scheme.{u}) (f : sourceOverlap C i j ⟶ Z),
      (∀ g : G, (act g).hom ≫ f = f) →
        ∃! u : Q.W (i, j) ⟶ Z, quotientMap D ≫ u = f) :
    AffineOverlapQuotientData C Q i j act where
  W_affine := D.W_affine
  π := quotientMap D
  invariant := hinv
  universal := huniv

end AffineOverlapCoordinateData

/-- The coordinate residual for all chart overlaps, with fixed actual action. -/
def AffineOverlapCoordinateResidual
    (C : SourceChartFamily) (Q : QuotientChartGluingData C) : Prop :=
  ∀ (i j : C.J) (act : G →* CategoryTheory.Aut (sourceOverlap C i j)),
    ∃ D : AffineOverlapCoordinateData (R := R) (G := G) C Q i j act,
      (∀ g : G,
        (act g).hom ≫ AffineOverlapCoordinateData.quotientMap D =
          AffineOverlapCoordinateData.quotientMap D) ∧
      (∀ (Z : Scheme.{u}) (f : sourceOverlap C i j ⟶ Z),
        (∀ g : G, (act g).hom ≫ f = f) →
          ∃! u : Q.W (i, j) ⟶ Z,
            AffineOverlapCoordinateData.quotientMap D ≫ u = f)

/-- The affine overlap quotient family residual. -/
def AffineOverlapQuotientFamilyResidual
    (C : SourceChartFamily) (Q : QuotientChartGluingData C) : Prop :=
  ∀ (i j : C.J) (act : G →* CategoryTheory.Aut (sourceOverlap C i j)),
    Nonempty (AffineOverlapQuotientData C Q i j act)

/-- Coordinate data gives the affine overlap quotient family. -/
theorem affineOverlapQuotientFamily_of_coordinateData
    (C : SourceChartFamily) (Q : QuotientChartGluingData C)
    (h : AffineOverlapCoordinateResidual (R := R) (G := G) C Q) :
    AffineOverlapQuotientFamilyResidual (G := G) C Q := by
  intro i j act
  obtain ⟨D, hinv, huniv⟩ := h i j act
  exact ⟨D.toAffineOverlapQuotientData hinv huniv⟩

/-- The affine overlap quotient residual. -/
def AffineOverlapQuotientResidual
    (C : SourceChartFamily) (Q : QuotientChartGluingData C) : Prop :=
  AffineOverlapQuotientFamilyResidual (G := G) C Q

/-- The coordinate residual closes the affine overlap quotient residual. -/
theorem affineOverlapQuotientResidual_of_coordinateData
    (C : SourceChartFamily) (Q : QuotientChartGluingData C)
    (h : AffineOverlapCoordinateResidual (R := R) (G := G) C Q) :
    AffineOverlapQuotientResidual (G := G) C Q :=
  affineOverlapQuotientFamily_of_coordinateData (R := R) (G := G) C Q h

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientDataFromInvariants
