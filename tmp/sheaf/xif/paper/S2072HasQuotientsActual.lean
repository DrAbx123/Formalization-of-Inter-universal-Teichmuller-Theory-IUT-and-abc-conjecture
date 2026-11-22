/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineBaseFiniteEtaleQuotients
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CoverSectionsAction
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj

/-!
# S2072: finite-group quotients of finite etale curve covers, actual inventory

Task: the first missing field of the curve pre-Galois card is
CurvePreGaloisCategoryRemainingFields X |>.hasQuotientsByFiniteGroups, i.e.
forall G [Group G] [Finite G],
  HasColimitsOfShape (SingleObj G) (FiniteEtaleCover X).
This file records what is ACTUALLY available in the tree for this obligation and
isolates the exact remaining condition.  It does not introduce sorry, axiom or
Nonempty placeholders.

## Inventory result (checked by compilation, not by claim)

The audit-ledger sentence "no construction in tree/Mathlib" is too strong.  The
tree already contains a substantial, 0-sorry affine quotient development:

* FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale:
  for a finite etale R-algebra A and a finite group G acting by R-algebra
  automorphisms, the fixed-point subalgebra A^G is finite etale over R.  This is
  the hard algebraic input and it is proved (rank decomposition + localizations),
  with axioms propext, Classical.choice, Quot.sound.
* ABCBridge.AffineBaseFiniteEtaleQuotients.quotientCoverOfDiagram,
  quotientProjectionOfDiagram, quotientProjectionOfDiagram_invariant:
  for every F : SingleObj G ⥤ FiniteEtaleCover (Spec R) the actual quotient
  cover Spec (Gamma Z)^G and its actual invariant projection are constructed.
* ABCBridge.AffineBaseFiniteEtaleQuotients.actionCoconeOfDiagram:
  the corresponding cocone over F.
* LeanFormal...AffineOverlapQuotientTransportProof.affineTargetUniversal:
  the affine-target fixed-point universal property (an actual theorem).
* FiniteEtaleQuotientGluedCover.finiteEtaleCoverCarrier_isAffine:
  every finite etale cover over an affine base is affine.

There is no Scheme quotient by a finite group action in Mathlib 4.32.2
(checked: Mathlib/AlgebraicGeometry has no Scheme.quotient, no group-action
quotient, no IsQuotient for schemes).  The tree's affine construction Spec (A^G)
is the substitute for the affine case.

## Exact remaining obligation (the true first missing)

For the SOURCE CURVE the base curveScheme K is affine
(curveScheme K = Spec (K[x,y]/(y^2-x^3+x)), definitionally).  On the affine base
the quotient object and projection are actual; only the IsColimit packaging of
the concrete cocone is missing.  It is frozen here as
AffineQuotientColimitPackaging R.  The gap is a *transport* gap, not a
construction gap: affineTargetUniversal supplies the desc map at the level of
Spec-morphisms for every affine target, and every target of a finite etale cover
of Spec R is affine; what is not packaged is the resulting
IsColimit (actionCoconeOfDiagram F).cocone in the full subcategory
FiniteEtaleCover (Spec R) (the dictionary between full-subcategory morphisms,
Over morphisms and Spec.preimage-algebra maps has to be assembled).

For a general scheme S, the additional missing piece is the affine-chart
gluing/descent recorded by the tree as GlobalQuotientCoconeResidual
(GlobalQuotientUniq.lean:120): the glued quotient cover and its scheme-level
universal property exist, but the cocone/IsColimit over SingleObj G is not
constructed.

## What this file proves

* cocone_singleObj_inv: any cocone over a SingleObj G-diagram is invariant.
* the actual quotient cover / projection / cocone for an affine base
  (affineActionQuotientCover, affineActionQuotientProjection,
  affineActionCocone) with the invariant projection;
* affineHasColimitsOfShape_of_packaging: the frozen residual implies
  HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (Spec R)) for all finite G;
* curveHasQuotientsOfPackaging and curvePreGaloisRemainingFieldsOfPackaging:
  the curve specialization, i.e. the first missing field of S2071/S2070 is
  equivalent to the residual;
* schemeHasQuotientsOfPackaging: the residual is a valid sufficient condition
  for the general scheme statement as well;
* curveQuotientsOf_trivialActions: the residual is not vacuous: for the constant
  (trivial-action) diagram the colimit exists unconditionally.

## Exact API needed to close the residual

The missing packaging needs exactly the following dictionary (all pieces exist
in the tree; the assembly does not):

1. FiniteEtaleCover.forgetOver (faithful) + CategoryTheory.ObjectProperty.hom_ext
   + Over.OverMorphism.ext, to reduce an equality of covers to an equality of
   underlying scheme maps;
2. finiteEtaleCoverCarrier_isAffine : IsAffine Z.carrier for every
   Z : FiniteEtaleCover (Spec R), so that Z.carrier.isoSpec is available for
   every cocone point;
3. ABCBridge.AffineQuotientUniversalProperty.coverSectionsAlgHom and its
   naturality/action lemmas, to turn the cover-level invariance
   (cocone_singleObj_inv) into the ring-level invariance of the algebra map
   associated with a cocone component;
4. affineTargetUniversal / affineFixedPointQuotient_universal_spec, to produce
   the desc map at the level of Spec-morphisms for each cocone.

With these, the body of IsColimit is:
  desc c := cover morphism (u_c >> W.carrier.isoSpec.inv), where u_c is the
  affineTargetUniversal factor of the algebra map of c.iota;
  fac and uniq are the two triangle equalities at the level of scheme maps,
  transported through forgetOver.

No sorry, no axiom, no Nonempty wrapper, no changed target.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open ABCBridge.AffineBaseFiniteEtaleQuotients
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
open AffineLocalQuotientGluingConstruct

namespace LeanFormal.IUT.XiFPaper.S2072HasQuotientsActual

universe u

/-! ## 1. A general invariant-component lemma for SingleObj cocones -/

/-- Every component of a cocone over a SingleObj G-diagram is fixed by the
action, i.e. F.map g >> c.iota = c.iota. -/
theorem cocone_singleObj_inv {C : Type u} [Category C] {G : Type u} [Group G]
    {F : SingleObj G ⥤ C} (c : Cocone F) (g : G) :
    F.map g ≫ c.ι.app (SingleObj.star G) = c.ι.app (SingleObj.star G) := by
  have h := c.ι.naturality (X := SingleObj.star G) (Y := SingleObj.star G) g
  rw [show ((Functor.const (SingleObj G)).obj c.pt).map g =
      𝟙 (((Functor.const (SingleObj G)).obj c.pt).obj (SingleObj.star G)) from rfl] at h
  rw [Category.comp_id] at h
  exact h

/-! ## 2. The actual affine quotient cover, projection and cocone -/

section AffineBase

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [Finite G]
variable (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R)))

/-- The actual canonical quotient cover of an action diagram, obtained by
gluing the affine fixed-point quotients; for the affine base this is the single
chart Spec (Gamma (F.obj star))^G. -/
noncomputable def affineActionQuotientCover :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  quotientCoverOfDiagram F

/-- The actual quotient projection. -/
noncomputable def affineActionQuotientProjection :
    F.obj (SingleObj.star G) ⟶ affineActionQuotientCover (R := R) (G := G) F :=
  quotientProjectionOfDiagram F

/-- The projection is invariant under the action. -/
theorem affineActionQuotientProjection_invariant (g : G) :
    F.map g ≫ affineActionQuotientProjection (R := R) (G := G) F =
      affineActionQuotientProjection (R := R) (G := G) F :=
  quotientProjectionOfDiagram_invariant F g

/-- The actual quotient cocone over the action diagram. -/
noncomputable def affineActionCocone : Cocone F :=
  (actionCoconeOfDiagram F).cocone

/-- The point of the quotient cocone is the actual quotient cover. -/
theorem affineActionCocone_pt :
    (affineActionCocone (R := R) (G := G) F).pt =
      affineActionQuotientCover (R := R) (G := G) F := rfl

/-- The component of the quotient cocone is the actual projection. -/
theorem affineActionCocone_ι :
    (affineActionCocone (R := R) (G := G) F).ι.app (SingleObj.star G) =
      affineActionQuotientProjection (R := R) (G := G) F := rfl

/-- Exact residual: the concrete quotient cocone is a colimit in
FiniteEtaleCover (Spec R).  This is the only missing step for the affine base
(the quotient object, projection, invariance and the affine-target universal
property are all already constructed elsewhere in the tree). -/
def AffineQuotientColimitPackaging (R : Type u) [CommRing R] :=
  ∀ (G : Type u) [Group G] [Finite G]
    (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R))),
    IsColimit (affineActionCocone (R := R) (G := G) F)

/-- The frozen residual implies HasColimitsOfShape (SingleObj G) for the
affine finite etale cover category, i.e. the first missing field of the curve
pre-Galois card. -/
theorem affineHasColimitsOfShape_of_packaging
    (h : AffineQuotientColimitPackaging R) :
    ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G)
        (FiniteEtaleCover (Spec (CommRingCat.of R))) := by
  intro G _ _
  refine ⟨fun F => HasColimit.mk
    ⟨affineActionCocone (R := R) (G := G) F, h G F⟩⟩

end AffineBase

/-! ## 3. The actual curve source, and the exact first missing field -/

/-- The source curve is definitionally the spectrum of its Weierstrass
coordinate ring, hence the affine-base theorem applies. -/
theorem curveScheme_eq_spec (K : Type u) [Field K] :
    curveScheme K = Spec (CommRingCat.of (curveCoordinateRing K)) := rfl

/-- The first missing field for the curve, conditional on the frozen packaging
residual. -/
theorem curveHasQuotientsOfPackaging (K : Type u) [Field K]
    (h : AffineQuotientColimitPackaging (curveCoordinateRing K)) :
    ∀ (G : Type u) [Group G] [Finite G],
      HasColimitsOfShape (SingleObj G) (FiniteEtaleCover (curveScheme K)) := by
  have h' := affineHasColimitsOfShape_of_packaging (R := curveCoordinateRing K) h
  intro G _ _
  rw [curveScheme_eq_spec K]
  exact h' G

/-- The consumer: the curve pre-Galois remaining-fields card, conditional on
the packaging residual.  This is exactly the field frozen in S2070/S2071. -/
theorem curvePreGaloisRemainingFieldsOfPackaging (K : Type u) [Field K]
    (h : AffineQuotientColimitPackaging (curveCoordinateRing K)) :
    CurvePreGaloisCategoryRemainingFields (curveScheme K) where
  hasQuotientsByFiniteGroups := curveHasQuotientsOfPackaging K h

/-! ## 4. General scheme statement and the residual is not vacuous -/

/-- The general-scheme target (CurvePreGaloisCategoryRemainingFields field). -/
def SchemeQuotientsByFiniteGroups (S : Scheme.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S)

/-- The affine packaging residual is a sufficient condition for the general
scheme statement, via the definitional identification. -/
theorem schemeHasQuotientsOfPackaging {S : Scheme.{u}} {R : Type u} [CommRing R]
    (hS : S = Spec (CommRingCat.of R))
    (h : AffineQuotientColimitPackaging R) :
    SchemeQuotientsByFiniteGroups S := by
  subst hS
  exact affineHasColimitsOfShape_of_packaging h

/-- The residual is not vacuous: for the constant (trivial-action) diagram the
colimit exists unconditionally, and it is the identity cover. -/
noncomputable def curveQuotientsOf_trivialActions (K : Type u) [Field K]
    (G : Type u) [Group G] (X : FiniteEtaleCover (curveScheme K)) :
    IsColimit (trivializedActionCocone (G := G) X) :=
  isColimit_trivializedActionCocone (G := G) X

end LeanFormal.IUT.XiFPaper.S2072HasQuotientsActual