/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors / S1843
-/
import tmp.sheaf.xif.paper.S1841SourceRepresentabilityActual

/-!
# S1843: the all-scheme-point base changes of a finite etale cover, and the exact
# first missing for affine representability of its source

## The question

For a cover A : S1728Cover = OrbicurveFiniteEtaleCover S1726Orbicurve, the
representable finite etaleness of A.map : A.source ⟶ X.stack supplies, for
**every** test scheme T and **every** point
p : h_T ⟶ X.stack = h_{Spec R'}, an actual base-change presentation

  A.finiteEtale.baseChange T p,

with a pullback scheme P_p, a projection pi_p : P_p ⟶ T that is finite and
etale, a 1-cell t_p : h_{P_p} ⟶ A.source, a 2-commutative square and a weak
two-pullback witness (the recorded TwoPullbackWitness).

S1841 (with S1827, S1804, S1801) showed that the *single* identity-point square
does not, from its seven recorded fields alone, give the missing half of the
2-universal property, and that the exact first missing statement is
S1841FirstMissing (equivalently S1756Unit, S1804FirstMissing, the fullness of
the cone comparison of the identity-point square, or S1756End = 1).

The question of this file is whether the **all-points** data -- each point
having its own scheme presentation with finite etale projection -- together with
the stack property of A.source already forces S1841FirstMissing, without
changing TwoPullbackWitness.

## What is proved here (unconditionally)

1. S1843AllPointBaseChanges: for every cover and every test-scheme point there
   is a base-change presentation, and its projection is finite etale
   (S1843AllPoint_finiteEtale).  This is the all-scheme-points premise, stated
   with the actual recorded structures.

2. S1843PointSurj: **every object of the cover source over any test scheme T is
   the image of a T-point of the affine model S_A**: for every
   x : h_T ⟶ A.source there is s : h_T ⟶ h_{S_A} with s >> toSource ~ x.
   This is the object-level (essential surjectivity) content of "the source is
   represented by the model", and it follows from the weak witness at the
   single identity point.

3. **Exact new characterisations of the remaining gap.**  Define

   * S1843PointSeparated A: the comparison toSource is injective on
     test-scheme points: any two T-points of S_A with isomorphic images in
     A.source are themselves isomorphic (i.e. equal, h_{S_A} being
     representable);
   * S1843ToSourceRightCancel A: toSource is right-cancellable, i.e. a 1-cell
     into S_A is determined up to 2-isomorphism by its composite with toSource.

   Then

       S1841FirstMissing  ↔  (∀ A, S1843PointSeparated A)
                          ↔  (∀ A, S1843ToSourceRightCancel A);

   and, for each cover, these are equivalent to the full cone comparison
   S1827ConeEssSurj of the recorded identity-point square
   (S1843ConeEssSurj_iff_pointSeparated, S1843ConeEssSurj_iff_rightCancel).

   So the *whole* remaining content of affine representability, after the
   automatic object-level surjectivity, is point separation (equivalently right
   cancellation) of the identity-point comparison.  This is the precise first
   missing statement in geometric form.

4. **The recorded weak-witness fields alone cannot supply the separation.**
   S1843RightCancelOf is the right-cancellation form of the missing half for an
   arbitrary square with a recorded weak witness.  The S1801 degenerate square
   satisfies all seven recorded fields, yet its first leg is not
   right-cancellable (S1843RightCancelNotFromWitness).  Hence no argument from
   the recorded fields alone -- at the identity point or at any point -- can
   give S1843ToSourceRightCancel; an input strictly beyond the recorded weak
   witness fields is necessary.

5. S1843AllPointsFull: if *every* point's presentation were a full
   two-pullback (the missing half at all points), then the identity point is one
   of them and S1841FirstMissing follows
   (S1843FirstMissing_of_allPointsFull).  Conversely the identity-point full
   property is exactly S1841QuasiEquiv (S1756ToSource A)
   (S1843IdentityPoint_full_iff).  So the only usable all-points strengthening
   is the one that already contains the identity point's missing half; the
   recorded all-points *weak* fields do not by themselves provide it.

## Honest verdict

S1841FirstMissing is **not proved** here, and no fake 2-cell, equivalence or
axiom is introduced.  What is new relative to S1841 is:

* the all-points presentations are formalised and their finite-etale content is
  extracted unconditionally;
* the object-level surjectivity of the comparison at every scheme point is
  proved unconditionally;
* the remaining gap is characterised exactly as the *separation* (right
  cancellation) of the comparison -- a genuinely different and more geometric
  form of the missing statement than "the identity-point square is a full
  pullback";
* the weak-witness schema is shown not to imply that separation.

Thus the all-points weak base-change data plus the stack property of the source
prove that every object of the source comes from the model; the seven
recorded witness fields do not by themselves exclude extra identifications
inside the source fiber, and that exclusion is exactly the remaining input (it is not a
consequence of the seven recorded witness fields alone, as S1801 shows).

No descent computation along the all-points schemes is used here: the
two-pullback witnesses live at the level of pseudofunctors, and the stack
condition A.source.isStack is not consumed by the arguments below.  This is
itself part of the finding: EtaleStackBaseChangePresentation has no field
relating its presentations at different points, so the recorded all-points
data does not by itself supply a new 2-cell at the identity point; the only
strengthening formalised here that closes the target is the full 2-universal
property at that point (S1843AllPointsFull).  No sorry, no new axiom, no Shrink, ULift or PUnit is
used; the axiom footprint is propext, Classical.choice and Quot.sound (see the
#print axioms block).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1843SourceAllPointsActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1784SourceRetractionUnitActual
open LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1831StrongSquareGeometricActual
open LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual

/-! ## 1. The all-points base-change presentations -/

/-- The all-points base-change data of a cover: for every test scheme T and
every point p : h_T ⟶ X.stack of the represented base, the representable
finite etaleness of A.map supplies an actual base-change presentation. -/
def S1843AllPointBaseChanges (A : S1728Cover) : Prop :=
  ∀ (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber),
    Nonempty (EtaleStackBaseChangePresentation A.map T p)

/-- Every scheme point has a base-change presentation. -/
theorem S1843AllPointBaseChanges_holds (A : S1728Cover) :
    S1843AllPointBaseChanges A :=
  fun T p => ⟨A.finiteEtale.baseChange T p⟩

/-- The projection of every scheme-point base change is finite and etale. -/
theorem S1843AllPoint_finiteEtale (A : S1728Cover)
    (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber) :
    IsFinite ((A.finiteEtale.baseChange T p).projection.left) ∧
      Etale ((A.finiteEtale.baseChange T p).projection.left) :=
  A.finiteEtale.hasProperty T p

/-- Scheme-level form of the all-points data: a pullback scheme with a finite
etale projection, for every scheme point. -/
theorem S1843AllPoint_pullbackScheme (A : S1728Cover)
    (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber) :
    ∃ (P : SchemeOverField S1726K) (π : P ⟶ T)
      (t : Pseudofunctor.StrongTrans (S1743Y P) (S1743Source A)),
      IsFinite π.left ∧ Etale π.left := by
  let B := A.finiteEtale.baseChange T p
  exact ⟨B.pullbackScheme, B.projection, B.toSource, A.finiteEtale.hasProperty T p⟩

/-- The identity point of the represented base is the presentation used by
S1733/S1743; its projection is the finite etale structure morphism of the
affine model. -/
theorem S1843IdentityPoint_finiteEtale (A : S1728Cover) :
    IsFinite (S1756Projection A).left ∧ Etale (S1756Projection A).left :=
  A.finiteEtale.hasProperty S1726AffineOver S1733BasePoint

/-! ## 2. All objects of the source come from the affine model

The weak universal property of the identity-point square, applied to the cone
built from an arbitrary point of the source, already gives essential
surjectivity of the comparison at every test scheme.  No extra input is needed
for this half. -/

/-- The cone over the recorded identity-point square attached to a point
x : h_T ⟶ A.source: its two legs are x and x >> A.map. -/
noncomputable def S1843PointCone (A : S1728Cover)
    (T : SchemeOverField S1726K)
    (x : Pseudofunctor.StrongTrans (S1743Y T) (S1743Source A)) :
    (S1743Square A).Cone (S1743Y T) where
  toX := x
  toY := Pseudofunctor.StrongTrans.vcomp x A.map
  commutes :=
    (S1756RightUnitorIso (Pseudofunctor.StrongTrans.vcomp x A.map)).symm

/-- The lift of that cone: the corresponding point of the affine model. -/
noncomputable def S1843PointLift (A : S1728Cover)
    (T : SchemeOverField S1726K)
    (x : Pseudofunctor.StrongTrans (S1743Y T) (S1743Source A)) :
    Pseudofunctor.StrongTrans (S1743Y T) (S1743ModelStack A) :=
  (S1743BaseChange A).isPullback.lift (S1743Y T) (S1843PointCone A T x)

/-- The lifted point maps to the given point of the source. -/
theorem S1843PointLift_toSource (A : S1728Cover)
    (T : SchemeOverField S1726K)
    (x : Pseudofunctor.StrongTrans (S1743Y T) (S1743Source A)) :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp (S1843PointLift A T x) (S1756ToSource A))
      x) :=
  ⟨(S1743BaseChange A).isPullback.liftToX (S1743Y T) (S1843PointCone A T x)⟩

/-- **Object-level surjectivity of the comparison at every scheme point**: every
object of the cover source over T is the image of a T-point of the affine model
S_A.  This is the unconditional all-points half of representability. -/
theorem S1843PointSurj (A : S1728Cover)
    (T : SchemeOverField S1726K)
    (x : Pseudofunctor.StrongTrans (S1743Y T) (S1743Source A)) :
    ∃ s : Pseudofunctor.StrongTrans (S1743Y T) (S1743ModelStack A),
      Nonempty (Iso
        (Pseudofunctor.StrongTrans.vcomp s (S1756ToSource A)) x) :=
  ⟨S1843PointLift A T x, S1843PointLift_toSource A T x⟩

/-- The all-points form of the same statement: for every point of the source at
every test scheme there is a model point with the same image. -/
theorem S1843AllPoint_surj (A : S1728Cover)
    (T : SchemeOverField S1726K) :
    ∀ x : Pseudofunctor.StrongTrans (S1743Y T) (S1743Source A),
      ∃ s : Pseudofunctor.StrongTrans (S1743Y T) (S1743ModelStack A),
        Nonempty (Iso
          (Pseudofunctor.StrongTrans.vcomp s (S1756ToSource A)) x) :=
  fun x => S1843PointSurj A T x

/-! ## 3. The exact remaining gap: separation of the comparison -/

/-- **Point separation of the comparison**: the identity-point comparison is
injective on test-scheme points up to 2-isomorphism.  Any two points of the
affine model with isomorphic images in the source are already isomorphic
(equivalently equal, since the model is representable). -/
def S1843PointSeparated (A : S1728Cover) : Prop :=
  ∀ (U : SchemeOverField S1726K)
    (x y : Pseudofunctor.StrongTrans (S1743Y U) (S1743ModelStack A)),
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp x (S1756ToSource A))
      (Pseudofunctor.StrongTrans.vcomp y (S1756ToSource A))) →
    Nonempty (Iso x y)

/-- **Right cancellation of the comparison**: a 1-cell into the affine model is
determined up to 2-isomorphism by its composite with toSource.  This is the
2-categorical form of point separation. -/
def S1843ToSourceRightCancel (A : S1728Cover) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K)
    (f g : Pseudofunctor.StrongTrans W (S1743ModelStack A)),
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp f (S1756ToSource A))
      (Pseudofunctor.StrongTrans.vcomp g (S1756ToSource A))) →
    Nonempty (Iso f g)

/-- A quasi-equivalence of the comparison gives point separation. -/
theorem S1843PointSeparated_of_quasiEquiv (A : S1728Cover)
    (h : S1841QuasiEquiv (S1756ToSource A)) :
    S1843PointSeparated A := by
  obtain ⟨inv, hu, _⟩ := h
  have hu' : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) := hu.some
  intro U x y e
  have h1 : Iso x (Pseudofunctor.StrongTrans.vcomp x
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) :=
    (S1756RightUnitorIso x).symm
  have h2 : Iso
      (Pseudofunctor.StrongTrans.vcomp x (Pseudofunctor.StrongTrans.id (S1743ModelStack A)))
      (Pseudofunctor.StrongTrans.vcomp x
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv)) :=
    (S1756WhiskerLeftIso x (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) hu').symm
  have h3 : Iso
      (Pseudofunctor.StrongTrans.vcomp x
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp x (S1756ToSource A)) inv) :=
    (S1756AssociatorIso x (S1756ToSource A) inv).symm
  have h4 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp x (S1756ToSource A)) inv)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp y (S1756ToSource A)) inv) :=
    S1756WhiskerRightIso _ _ inv e.some
  have h5 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp y (S1756ToSource A)) inv)
      (Pseudofunctor.StrongTrans.vcomp y
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv)) :=
    S1756AssociatorIso y (S1756ToSource A) inv
  have h6 : Iso
      (Pseudofunctor.StrongTrans.vcomp y
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv))
      (Pseudofunctor.StrongTrans.vcomp y
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) :=
    S1756WhiskerLeftIso y (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) hu'
  have h7 : Iso
      (Pseudofunctor.StrongTrans.vcomp y (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) y :=
    S1756RightUnitorIso y
  exact ⟨h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))⟩

/-- A quasi-equivalence of the comparison is right-cancellable. -/
theorem S1843RightCancel_of_quasiEquiv (A : S1728Cover)
    (h : S1841QuasiEquiv (S1756ToSource A)) :
    S1843ToSourceRightCancel A := by
  obtain ⟨inv, hu, _⟩ := h
  have hu' : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) := hu.some
  intro W f g e
  have h1 : Iso f (Pseudofunctor.StrongTrans.vcomp f
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) :=
    (S1756RightUnitorIso f).symm
  have h2 : Iso
      (Pseudofunctor.StrongTrans.vcomp f (Pseudofunctor.StrongTrans.id (S1743ModelStack A)))
      (Pseudofunctor.StrongTrans.vcomp f
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv)) :=
    (S1756WhiskerLeftIso f (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) hu').symm
  have h3 : Iso
      (Pseudofunctor.StrongTrans.vcomp f
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp f (S1756ToSource A)) inv) :=
    (S1756AssociatorIso f (S1756ToSource A) inv).symm
  have h4 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp f (S1756ToSource A)) inv)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp g (S1756ToSource A)) inv) :=
    S1756WhiskerRightIso _ _ inv e.some
  have h5 : Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp g (S1756ToSource A)) inv)
      (Pseudofunctor.StrongTrans.vcomp g
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv)) :=
    S1756AssociatorIso g (S1756ToSource A) inv
  have h6 : Iso
      (Pseudofunctor.StrongTrans.vcomp g
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv))
      (Pseudofunctor.StrongTrans.vcomp g
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) :=
    S1756WhiskerLeftIso g (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) inv)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) hu'
  have h7 : Iso
      (Pseudofunctor.StrongTrans.vcomp g (Pseudofunctor.StrongTrans.id (S1743ModelStack A))) g :=
    S1756RightUnitorIso g
  exact ⟨h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))⟩

/-- Right cancellation implies point separation. -/
theorem S1843PointSeparated_of_rightCancel (A : S1728Cover)
    (h : S1843ToSourceRightCancel A) : S1843PointSeparated A :=
  fun U x y e => h (S1743Y U) x y e

/-- Point separation forces the missing unit 2-cell: the self-map
toSource >> lift and the identity have the same composite with toSource (the
unconditional counit), so separation identifies them. -/
theorem S1843Unit_of_pointSeparated (A : S1728Cover)
    (h : S1843PointSeparated A) : S1756Unit A := by
  have hc : Iso
      (Pseudofunctor.StrongTrans.vcomp (S1743Lift A) (S1756ToSource A))
      (Pseudofunctor.StrongTrans.id (S1743Source A)) :=
    (S1743BaseChange A).isPullback.liftToX (S1743Source A) (S1743IdentityCone A)
  have hpre : Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
        (S1756ToSource A))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) (S1756ToSource A))) := by
    refine ⟨?_⟩
    exact (S1756AssociatorIso (S1756ToSource A) (S1743Lift A) (S1756ToSource A)).trans
      ((S1756WhiskerLeftIso (S1756ToSource A) _ _ hc).trans
        ((S1756RightUnitorIso (S1756ToSource A)).trans
          (S1756LeftUnitorIso (S1756ToSource A)).symm))
  exact h (S1733Model A)
    (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
    (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) hpre

/-- The missing unit gives the quasi-equivalence of the comparison (through
S1831's characterisation of the full 2-universal property). -/
theorem S1843QuasiEquiv_of_unit (A : S1728Cover) (h : S1756Unit A) :
    S1841QuasiEquiv (S1756ToSource A) :=
  (S1841ConeEssSurj_iff_quasiEquiv A).mp
    ((S1831StrongSquare_iff_unit A).mpr h)

/-- **Exact characterisation, point form**: affine representability of the cover
source is equivalent to point separation of the identity-point comparison. -/
theorem S1843FirstMissing_iff_pointSeparated :
    S1841FirstMissing ↔ ∀ A : S1728Cover, S1843PointSeparated A := by
  constructor
  · intro h A
    exact S1843PointSeparated_of_quasiEquiv A (h A)
  · intro h A
    exact S1843QuasiEquiv_of_unit A (S1843Unit_of_pointSeparated A (h A))

/-- **Exact characterisation, cancellation form**: affine representability of
the cover source is equivalent to right cancellation of the comparison. -/
theorem S1843FirstMissing_iff_rightCancel :
    S1841FirstMissing ↔ ∀ A : S1728Cover, S1843ToSourceRightCancel A := by
  constructor
  · intro h A
    exact S1843RightCancel_of_quasiEquiv A (h A)
  · intro h A
    exact S1843QuasiEquiv_of_unit A
      (S1843Unit_of_pointSeparated A
        (S1843PointSeparated_of_rightCancel A (h A)))

/-- The missing full 2-universal property of the identity-point square is
exactly point separation of the comparison.  This identifies the geometric
content of the first missing statement with a condition on test-scheme points
alone. -/
theorem S1843ConeEssSurj_iff_pointSeparated (A : S1728Cover) :
    S1827ConeEssSurj A ↔ S1843PointSeparated A := by
  constructor
  · intro h
    exact S1843PointSeparated_of_quasiEquiv A
      ((S1841ConeEssSurj_iff_quasiEquiv A).mp h)
  · intro h
    exact (S1841ConeEssSurj_iff_quasiEquiv A).mpr
      (S1843QuasiEquiv_of_unit A (S1843Unit_of_pointSeparated A h))

/-- The missing full 2-universal property is exactly right cancellation of the
comparison. -/
theorem S1843ConeEssSurj_iff_rightCancel (A : S1728Cover) :
    S1827ConeEssSurj A ↔ S1843ToSourceRightCancel A := by
  constructor
  · intro h
    exact S1843RightCancel_of_quasiEquiv A
      ((S1841ConeEssSurj_iff_quasiEquiv A).mp h)
  · intro h
    exact (S1843ConeEssSurj_iff_pointSeparated A).mpr
      (S1843PointSeparated_of_rightCancel A h)

/-! ## 4. The all-points full 2-universal property, and why the weak data is not enough -/

/-- The base-change square of the presentation at a scheme point p. -/
noncomputable def S1843PresentationSquare (A : S1728Cover)
    (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber) :
    EtalePseudofunctorSquare
      (S1743Y (A.finiteEtale.baseChange T p).pullbackScheme)
      (S1743Source A) (S1743Y T) S1726Orbicurve.stack.fiber :=
  EtalePseudofunctorSquare.mk (A.finiteEtale.baseChange T p).toSource
    (A.finiteEtale.baseChange T p).projectionMap.transformation A.map p
    (A.finiteEtale.baseChange T p).commutes

/-- The missing half of the 2-universal property at an arbitrary scheme point:
the cone comparison of that point's presentation is essentially surjective. -/
def S1843PresentationFull (A : S1728Cover)
    (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber) : Prop :=
  S1827EssSurjOf (S1843PresentationSquare A T p)
    (A.finiteEtale.baseChange T p).isPullback

/-- The all-points full 2-universal property. -/
def S1843AllPointsFull (A : S1728Cover) : Prop :=
  ∀ (T : SchemeOverField S1726K)
    (p : Pseudofunctor.StrongTrans (S1743Y T) S1726Orbicurve.stack.fiber),
    S1843PresentationFull A T p

/-- The identity-point presentation is the recorded one, so its full
2-universal property is exactly the quasi-equivalence of toSource. -/
theorem S1843IdentityPoint_full_iff (A : S1728Cover) :
    S1843PresentationFull A S1726AffineOver S1733BasePoint ↔
      S1841QuasiEquiv (S1756ToSource A) :=
  S1841ConeEssSurj_iff_quasiEquiv A

/-- If every point's presentation has the full 2-dimensional universal property,
then the identity point does, hence the cover source is represented by its
affine model.  This is the only all-points strengthening that closes the target;
it already contains the missing half at the identity point. -/
theorem S1843FirstMissing_of_allPointsFull
    (h : ∀ A : S1728Cover, S1843AllPointsFull A) : S1841FirstMissing := by
  intro A
  exact (S1843IdentityPoint_full_iff A).mp (h A S1726AffineOver S1733BasePoint)

/-- The right-cancellation form of the missing half for an arbitrary square with
a recorded weak two-pullback witness. -/
def S1843RightCancelOf {P X Y Z : EtaleStackPseudofunctor S1726K}
    (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K)
    (f g : Pseudofunctor.StrongTrans W P),
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp f sq.toX)
      (Pseudofunctor.StrongTrans.vcomp g sq.toX)) →
    Nonempty (Iso f g)

/-- **The recorded weak-witness fields do not imply right cancellation** (and
hence do not imply the missing essential surjectivity): S1801's degenerate
square satisfies all seven recorded fields, its first leg is the collapse to a
point, and the identity and the constant-at-zero endomorphism of the apex have
the same composite with that leg while not being 2-isomorphic. -/
theorem S1843RightCancelNotFromWitness :
    ¬ (∀ (P X Y Z : EtaleStackPseudofunctor S1726K)
        (sq : EtalePseudofunctorSquare P X Y Z) (w : sq.TwoPullbackWitness),
        S1843RightCancelOf sq w) := by
  intro h
  have hsq := h (S1801TwoStack S1726K) (S1801PointStack S1726K)
    (S1801PointStack S1726K) (S1801PointStack S1726K)
    (S1801DegenerateSquare S1726K) (S1801DegenerateWitness S1726K)
  exact S1801DegenerateNotIso S1726K
    (hsq (S1801TwoStack S1726K)
      (Pseudofunctor.StrongTrans.id (S1801TwoStack S1726K))
      (S1801ConstZero S1726K (S1801TwoStack S1726K))
      ⟨S1801IsoToOne S1726K _ _⟩)

/-- For a cover, the right-cancellation statement is precisely the instance of
the schema at the recorded identity-point square.  Hence the countermodel above
shows that the recorded fields of that square do not supply it: the missing
input is genuinely geometric, not a coherence of the given data. -/
theorem S1843ToSourceRightCancel_iff_schema (A : S1728Cover) :
    S1843ToSourceRightCancel A ↔
      S1843RightCancelOf (S1743Square A) (S1743BaseChange A).isPullback :=
  Iff.rfl

/-! ## 5. Summary of the exact first missing -/

/-- The exact first missing in its original form, in the two new forms of this
file: point separation and right cancellation of the identity-point comparison.
The all-points weak base-change data is not part of the conclusion: it is
unconditional (S1843AllPointBaseChanges_holds) and it supplies only the
object-level half (S1843PointSurj). -/
theorem S1843FirstMissing_characterisation :
    S1841FirstMissing ↔
      ((∀ A : S1728Cover, S1843PointSeparated A) ∧
        (∀ A : S1728Cover, S1843ToSourceRightCancel A)) :=
  S1843FirstMissing_iff_pointSeparated.trans
    (by
      constructor
      · intro h
        exact ⟨h, fun A => S1843RightCancel_of_quasiEquiv A
          (S1843QuasiEquiv_of_unit A
            (S1843Unit_of_pointSeparated A (h A)))⟩
      · rintro ⟨h, _⟩
        exact h)

/-- The precise first missing, stated as the remaining injectivity of the
comparison after the unconditional all-points surjectivity: every point of the
affine model is already determined by its image in the cover source. -/
def S1843FirstMissingPrecise : Prop :=
  ∀ A : S1728Cover, S1843PointSeparated A

/-- The precise first missing is exactly S1841's first missing. -/
theorem S1843FirstMissingPrecise_iff :
    S1841FirstMissing ↔ S1843FirstMissingPrecise :=
  S1843FirstMissing_iff_pointSeparated


/-! ## 6. Checks and axiom audit -/

#check S1843AllPointBaseChanges
#check S1843AllPointBaseChanges_holds
#check S1843AllPoint_finiteEtale
#check S1843AllPoint_pullbackScheme
#check S1843IdentityPoint_finiteEtale
#check S1843PointCone
#check S1843PointLift
#check S1843PointLift_toSource
#check S1843PointSurj
#check S1843PointSeparated
#check S1843ToSourceRightCancel
#check S1843PointSeparated_of_quasiEquiv
#check S1843RightCancel_of_quasiEquiv
#check S1843PointSeparated_of_rightCancel
#check S1843Unit_of_pointSeparated
#check S1843QuasiEquiv_of_unit
#check S1843FirstMissing_iff_pointSeparated
#check S1843FirstMissing_iff_rightCancel
#check S1843ConeEssSurj_iff_pointSeparated
#check S1843ConeEssSurj_iff_rightCancel
#check S1843PresentationSquare
#check S1843PresentationFull
#check S1843AllPointsFull
#check S1843IdentityPoint_full_iff
#check S1843FirstMissing_of_allPointsFull
#check S1843RightCancelOf
#check S1843RightCancelNotFromWitness
#check S1843ToSourceRightCancel_iff_schema
#check S1843FirstMissing_characterisation
#check S1843FirstMissingPrecise
#check S1843FirstMissingPrecise_iff

#print axioms S1843AllPointBaseChanges_holds
#print axioms S1843AllPoint_finiteEtale
#print axioms S1843AllPoint_pullbackScheme
#print axioms S1843PointCone
#print axioms S1843PointLift_toSource
#print axioms S1843PointSurj
#print axioms S1843PointSeparated_of_quasiEquiv
#print axioms S1843RightCancel_of_quasiEquiv
#print axioms S1843Unit_of_pointSeparated
#print axioms S1843QuasiEquiv_of_unit
#print axioms S1843FirstMissing_iff_pointSeparated
#print axioms S1843FirstMissing_iff_rightCancel
#print axioms S1843ConeEssSurj_iff_pointSeparated
#print axioms S1843ConeEssSurj_iff_rightCancel
#print axioms S1843IdentityPoint_full_iff
#print axioms S1843FirstMissing_of_allPointsFull
#print axioms S1843RightCancelNotFromWitness
#print axioms S1843ToSourceRightCancel_iff_schema
#print axioms S1843FirstMissing_characterisation
#print axioms S1843FirstMissingPrecise_iff

end LeanFormal.IUT.XiFPaper.S1843SourceAllPointsActual