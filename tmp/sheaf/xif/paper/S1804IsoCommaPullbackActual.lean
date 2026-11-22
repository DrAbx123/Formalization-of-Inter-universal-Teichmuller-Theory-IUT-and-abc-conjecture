/-
# S1804: the actual iso-comma 2-pullback of (A.map, id), and the precise first missing

## Context

For a cover A : S1728Cover, the identity-point base-change square is

    P = Y(S_A) --toSource--> X = A.source
       |                         |
      toY                       A.map
       v                         v
    Y = Y(Spec R') --id--> Z = Y(Spec R')

where the right leg is the identity (S1733BasePoint = id), so the cospan is
(A.map, id).  The recorded TwoPullbackWitness supplies only

  lift, liftToX, liftToY, liftTwoCell, liftTwoCell_toX, liftTwoCell_toY,
  twoCell_ext.

S1784 isolated the missing half as S1784LiftEssSurj: any 1-cell f whose two
projections agree with a cone is 2-isomorphic to the lift of that cone.  S1784
proved that this closes S1756FirstMissing, but did not prove the converse.

## What this file proves

1. The genuine iso-comma fiber of (A.map, id) at a test object U is the comma
   category with objects (x, y, h) where x : source(U), y : base(U) and
   h : A.map(x) -> y.  Since base(U) = Discrete(U -> Spec R'), every such h is
   an isomorphism; this is the requested (x, y, A.map(x) = y) model.  The
   projection to the source is proved full, faithful and essentially
   surjective, hence the iso-comma fiber is equivalent to the source fiber.

2. The actual 2-pullback of the cospan (A.map, id) is the source itself: the
   square S1804SourceSquare has X as apex, with projections id_X and A.map.
   Its lift of a cone c is c.toX, and this satisfies 1-cell uniqueness
   (S1804Source_isPullback), the same property S1784LiftEssSurj asks of the
   recorded square.  So the pullback is constructed, not assumed.

3. The recorded square is the actual pullback exactly when the canonical
   comparison toSource : P -> X is an equivalence, i.e. when the missing unit
   toSource ; lift = id_P exists.  We prove the new equivalence

     S1784LiftEssSurj A  <->  S1756Unit A  <->  S1758LiftConeIso A,

   upgrading S1784's one-way closure to an exact characterisation.  The
   forward direction uses S1784; the converse lifts any 2-isomorphism of
   toSource-whiskerings along the unit, using only the two triangle
   isomorphisms.

4. Consequently the missing statements are all equivalent:

     S1804FirstMissing  <->  S1756FirstMissing
                        <->  S1743SourceRetraction
                        <->  S1758FirstMissing.

   From S1804FirstMissing the quasi-equivalence P = X, S1756SourceRepresentableAll
   and the S1743 retraction follow.

## Honest boundary

No inhabitant of S1804FirstMissing is constructed, and no fake 2-cell or
equivalence is introduced.  The seven recorded fields do not imply it (S1784
records the Cat countermodel).  What is new here is that the missing statement
is now proved equivalent to the natural one (the comparison of the recorded
pullback with the actual pullback of (A.map, id), whose apex is the source),
and that the iso-comma fiber has been constructed and proved equivalent to the
source fiber.  The pseudofunctor-level packaging of the iso-comma is not
constructed separately: by item 2 the actual pullback pseudofunctor is the
source itself, and its fibers are the iso-comma categories of item 1.

## Axiom footprint

Only propext, Classical.choice and Quot.sound; see the #print axioms block.
No sorry, no new axiom, no Shrink, ULift or PUnit.
-/

import tmp.sheaf.xif.paper.S1784SourceRetractionUnitActual
import tmp.sheaf.xif.paper.S1758SourceRetractionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1804IsoCommaPullbackActual

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
open LeanFormal.IUT.XiFPaper.S1758SourceRetractionActual

/-! ## 1. The iso-comma fiber of (A.map, id) -/

abbrev S1804BaseFiber (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) : Type :=
  Discrete (Opposite.unop U.as ⟶ S1726AffineOver)

abbrev S1804SourceFiber (A : S1728Cover)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) : Type :=
  ↑((S1743Source A).obj U)

abbrev S1804MapFunctor (A : S1728Cover)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    S1804SourceFiber A U ⥤ S1804BaseFiber U :=
  (A.map.app U).toFunctor

def S1804BaseId (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    S1804BaseFiber U ⥤ S1804BaseFiber U where
  obj x := x
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev S1804IsoCommaFiber (A : S1728Cover)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) : Type :=
  Comma (S1804MapFunctor A U) (S1804BaseId U)

def S1804IsoCommaProj (A : S1728Cover)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    S1804IsoCommaFiber A U ⥤ S1804SourceFiber A U :=
  Comma.fst _ _

instance S1804IsoCommaProjFull (A : S1728Cover)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (S1804IsoCommaProj A U).Full where
  map_surjective {X Y} f :=
    ⟨{ left := f
       right :=
         (Discrete.eqToIso (Discrete.eq_of_hom X.hom).symm).hom ≫
           (S1804MapFunctor A U).map f ≫ Y.hom
       w := Subsingleton.elim _ _ }, rfl⟩

instance S1804IsoCommaProjFaithful (A : S1728Cover)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (S1804IsoCommaProj A U).Faithful where
  map_injective {X Y} f g h := by
    apply Comma.hom_ext
    · exact h
    · exact Subsingleton.elim _ _

instance S1804IsoCommaProjEssSurj (A : S1728Cover)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (S1804IsoCommaProj A U).EssSurj where
  mem_essImage x :=
    ⟨Comma.mk x ((S1804MapFunctor A U).obj x) (𝟙 _), ⟨Iso.refl x⟩⟩

instance S1804IsoCommaProjIsEquivalence (A : S1728Cover)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (S1804IsoCommaProj A U).IsEquivalence where

noncomputable def S1804IsoCommaFiberEquiv (A : S1728Cover)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    S1804IsoCommaFiber A U ≌ S1804SourceFiber A U :=
  (S1804IsoCommaProj A U).asEquivalence

/-! ## 1b. The named actual pullback object -/

/-- The actual 2-pullback object of the cospan (A.map, id).  Its apex is the
cover source itself; the explicit iso-comma description is the fiber
equivalence S1804IsoCommaFiberEquiv below.  This is not an assumption: the
universal property is proved in Section 2. -/
noncomputable abbrev S1804IsoCommaPullback (A : S1728Cover) :
    EtaleStackPseudofunctor S1726K :=
  S1743Source A

/-- The fiber of the actual pullback is equivalent to the iso-comma fiber
(x, y, h : A.map(x) -> y). -/
theorem S1804IsoCommaPullback_fiber (A : S1728Cover)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    Nonempty (S1804IsoCommaFiber A U ≌ (S1804IsoCommaPullback A).obj U) :=
  ⟨S1804IsoCommaFiberEquiv A U⟩

/-! ## 2. The actual 2-pullback of (A.map, id) is the source -/

noncomputable def S1804SourceSquare (A : S1728Cover) :
    EtalePseudofunctorSquare (S1743Source A) (S1743Source A)
      (S1743Y S1726AffineOver) (S1726Orbicurve.stack.fiber) where
  toX := Pseudofunctor.StrongTrans.id (S1743Source A)
  toY := A.map
  xToBase := A.map
  yToBase := S1733BasePoint
  commutes := (S1756LeftUnitorIso A.map).trans (S1756RightUnitorIso A.map).symm

noncomputable def S1804SourceCone (A : S1728Cover)
    {W : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans W (S1743Source A)) :
    (S1804SourceSquare A).Cone W where
  toX := f
  toY := Pseudofunctor.StrongTrans.vcomp f A.map
  commutes :=
    (S1756RightUnitorIso (Pseudofunctor.StrongTrans.vcomp f A.map)).symm

def S1804SourceLift (A : S1728Cover)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S1804SourceSquare A).Cone W) :
    Pseudofunctor.StrongTrans W (S1743Source A) :=
  c.toX

noncomputable def S1804SourceLiftToX (A : S1728Cover)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S1804SourceSquare A).Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1804SourceLift A c)
        (S1804SourceSquare A).toX) c.toX :=
  S1756RightUnitorIso c.toX

noncomputable def S1804SourceLiftToY (A : S1728Cover)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S1804SourceSquare A).Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1804SourceLift A c)
        (S1804SourceSquare A).toY) c.toY :=
  c.commutes.trans (S1756RightUnitorIso c.toY)

theorem S1804Source_isPullback (A : S1728Cover)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S1804SourceSquare A).Cone W)
    (f : Pseudofunctor.StrongTrans W (S1743Source A))
    (hX : Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp f (S1804SourceSquare A).toX) c.toX))
    (hY : Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp f (S1804SourceSquare A).toY) c.toY)) :
    Nonempty (Iso f (S1804SourceLift A c)) := by
  obtain ⟨e⟩ := hX
  exact ⟨(S1756RightUnitorIso f).symm.trans e⟩

theorem S1804SourceCone_proj (A : S1728Cover)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S1804SourceSquare A).Cone W) :
    (S1804SourceCone A c.toX).toX = c.toX ∧
      Nonempty (Iso (S1804SourceCone A c.toX).toY c.toY) :=
  ⟨rfl, ⟨c.commutes.trans (S1756RightUnitorIso c.toY)⟩⟩

/-! ## 3. The recorded square is the actual pullback exactly when the unit exists -/

theorem S1804LiftIsoOfUnit (A : S1728Cover) (h : S1756Unit A)
    {W : EtaleStackPseudofunctor S1726K}
    (f g : Pseudofunctor.StrongTrans W (S1743ModelStack A))
    (e : Iso (Pseudofunctor.StrongTrans.vcomp f (S1756ToSource A))
      (Pseudofunctor.StrongTrans.vcomp g (S1756ToSource A))) :
    Nonempty (Iso f g) := by
  obtain ⟨u⟩ := h
  refine ⟨?_⟩
  exact (S1756RightUnitorIso f).symm.trans
    ((S1756WhiskerLeftIso f (Pseudofunctor.StrongTrans.id (S1743ModelStack A))
        (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A)) u.symm).trans
      ((S1756AssociatorIso f (S1756ToSource A) (S1743Lift A)).symm.trans
        ((S1756WhiskerRightIso _ _ (S1743Lift A) e).trans
          ((S1756AssociatorIso g (S1756ToSource A) (S1743Lift A)).trans
            ((S1756WhiskerLeftIso g
                (Pseudofunctor.StrongTrans.vcomp (S1756ToSource A) (S1743Lift A))
                (Pseudofunctor.StrongTrans.id (S1743ModelStack A)) u).trans
              (S1756RightUnitorIso g))))))

theorem S1804LiftEssSurjOfUnit (A : S1728Cover) (h : S1756Unit A) :
    S1784LiftEssSurj A := by
  intro W c f hX hY
  obtain ⟨eX⟩ := hX
  exact S1804LiftIsoOfUnit A h f ((S1743BaseChange A).isPullback.lift W c)
    (eX.trans ((S1743BaseChange A).isPullback.liftToX W c).symm)

theorem S1804LiftEssSurj_iff_unit (A : S1728Cover) :
    S1784LiftEssSurj A ↔ S1756Unit A :=
  ⟨fun h => (S1756Unit_iff_end A).mpr (S1784End_eq_one_of_liftEssSurj A h),
    S1804LiftEssSurjOfUnit A⟩

theorem S1804LiftEssSurj_iff_end (A : S1728Cover) :
    S1784LiftEssSurj A ↔ S1756End A = 𝟙 (S1733Model A) :=
  (S1804LiftEssSurj_iff_unit A).trans (S1756Unit_iff_end A)

theorem S1804UnitOfLiftConeIso (A : S1728Cover)
    (h : S1758LiftConeIso A) : S1756Unit A := by
  obtain ⟨e1⟩ := h (S1743ModelStack A)
    (Pseudofunctor.StrongTrans.vcomp (S1758toSource A) (S1758Lift A))
  obtain ⟨e3⟩ := h (S1743ModelStack A) (𝟙 (S1743ModelStack A))
  exact ⟨e1.symm.trans ((S1758LiftTwoCellIso A).trans e3)⟩

theorem S1804LiftConeIso_iff_unit (A : S1728Cover) :
    S1758LiftConeIso A ↔ S1756Unit A :=
  ⟨S1804UnitOfLiftConeIso A,
    fun h => S1758LiftConeIso_of_retraction A h⟩

theorem S1804LiftEssSurj_iff_liftConeIso (A : S1728Cover) :
    S1784LiftEssSurj A ↔ S1758LiftConeIso A :=
  ⟨fun h => (S1804LiftConeIso_iff_unit A).mpr ((S1804LiftEssSurj_iff_unit A).mp h),
    fun h => (S1804LiftEssSurj_iff_unit A).mpr ((S1804LiftConeIso_iff_unit A).mp h)⟩

/-! ## 4. The precise first missing statement and its consequences -/

def S1804RecordedActual (A : S1728Cover) : Prop :=
  S1784LiftEssSurj A

def S1804FirstMissing : Prop := ∀ A : S1728Cover, S1804RecordedActual A

theorem S1804RecordedActual_iff_unit (A : S1728Cover) :
    S1804RecordedActual A ↔ S1756Unit A :=
  S1804LiftEssSurj_iff_unit A

theorem S1804RecordedActual_iff_end (A : S1728Cover) :
    S1804RecordedActual A ↔ S1756End A = 𝟙 (S1733Model A) :=
  S1804LiftEssSurj_iff_end A

theorem S1804FirstMissing_iff_S1756 :
    S1804FirstMissing ↔ S1756FirstMissing := by
  constructor
  · intro h A
    exact S1784End_eq_one_of_liftEssSurj A (h A)
  · intro h A
    exact (S1804RecordedActual_iff_unit A).mpr ((S1756Unit_iff_end A).mpr (h A))

theorem S1804FirstMissing_iff_S1758 :
    S1804FirstMissing ↔ S1758FirstMissing := by
  constructor
  · intro h A
    exact (S1804LiftConeIso_iff_unit A).mpr ((S1804RecordedActual_iff_unit A).mp (h A))
  · intro h A
    exact (S1804RecordedActual_iff_unit A).mpr ((S1804LiftConeIso_iff_unit A).mp (h A))

theorem S1804FirstMissing_iff_sourceRetraction :
    S1804FirstMissing ↔ S1743SourceRetraction :=
  S1804FirstMissing_iff_S1756.trans S1756Retraction_iff_firstMissing.symm

noncomputable def S1804StackEquivOfRecordedActual (A : S1728Cover)
    (h : S1804RecordedActual A) :
    S1756StackEquiv (S1743ModelStack A) (S1743Source A) :=
  S1756StackEquivOfUnit A ((S1804RecordedActual_iff_unit A).mp h)

/-- Actuality of the recorded presentation gives S1784's counit data: the lift
of the pullback's own cone is the identity and is 2-isomorphic to the
endomorphism toSource ; lift. -/
theorem S1804CounitData_of_recordedActual (A : S1728Cover)
    (h : S1804RecordedActual A) : S1784CounitData A := by
  have h' : S1784LiftEssSurj A := h
  constructor
  · obtain ⟨e⟩ := h' (S1743ModelStack A) (S1784PullbackCone A)
      (Pseudofunctor.StrongTrans.id (S1743ModelStack A))
      ⟨S1756LeftUnitorIso (S1756ToSource A)⟩
      ⟨S1756LeftUnitorIso (S1756ProjectionMap A)⟩
    exact ⟨e.symm⟩
  · obtain ⟨e⟩ := h' (S1743ModelStack A) (S1784PullbackCone A)
      (S1784EndTrans A) (S1784EndTrans_toSource A) (S1784EndTrans_projection A)
    exact ⟨e.symm⟩

/-- Conversely, S1784's counit data gives actuality of the recorded
presentation (through the endomorphism equation). -/
theorem S1804RecordedActual_of_counitData (A : S1728Cover)
    (h : S1784CounitData A) : S1804RecordedActual A :=
  (S1804LiftEssSurj_iff_end A).mpr (S1784End_eq_one_of_counitData A h)

/-- The missing essential surjectivity is exactly S1784's counit data. -/
theorem S1804RecordedActual_iff_counitData (A : S1728Cover) :
    S1804RecordedActual A ↔ S1784CounitData A :=
  ⟨S1804CounitData_of_recordedActual A, S1804RecordedActual_of_counitData A⟩

/-- The scheme-level consequence of actuality, through S1784's counit data. -/
theorem S1804End_eq_one_of_recordedActual (A : S1728Cover)
    (h : S1804RecordedActual A) : S1756End A = 𝟙 (S1733Model A) :=
  S1784End_eq_one_of_counitData A (S1804CounitData_of_recordedActual A h)

theorem S1804FirstMissing_to_S1756FirstMissing (h : S1804FirstMissing) :
    S1756FirstMissing :=
  S1804FirstMissing_iff_S1756.mp h

theorem S1804FirstMissing_to_sourceRetraction (h : S1804FirstMissing) :
    S1743SourceRetraction :=
  S1804FirstMissing_iff_sourceRetraction.mp h

theorem S1804FirstMissing_to_sourceRepresentableAll (h : S1804FirstMissing) :
    S1756SourceRepresentableAll :=
  S1784SourceRepresentableAll_of_liftEssSurj h

theorem S1804FirstMissing_iff_liftPointSurj :
    S1804FirstMissing ↔ ∀ A : S1728Cover, S1784LiftPointSurj A :=
  S1804FirstMissing_iff_S1756.trans S1784FirstMissing_iff_liftPointSurj

/-! ## 5. Checks -/

#check S1804BaseFiber
#check S1804SourceFiber
#check S1804MapFunctor
#check S1804IsoCommaFiber
#check S1804IsoCommaProj
#check S1804IsoCommaProjFull
#check S1804IsoCommaProjFaithful
#check S1804IsoCommaProjEssSurj
#check S1804IsoCommaFiberEquiv
#check S1804IsoCommaPullback
#check S1804IsoCommaPullback_fiber
#check S1804SourceSquare
#check S1804SourceCone
#check S1804SourceLift
#check S1804SourceLiftToX
#check S1804SourceLiftToY
#check S1804Source_isPullback
#check S1804SourceCone_proj
#check S1804LiftIsoOfUnit
#check S1804LiftEssSurjOfUnit
#check S1804LiftEssSurj_iff_unit
#check S1804LiftEssSurj_iff_end
#check S1804UnitOfLiftConeIso
#check S1804LiftConeIso_iff_unit
#check S1804LiftEssSurj_iff_liftConeIso
#check S1804RecordedActual
#check S1804FirstMissing
#check S1804FirstMissing_iff_S1756
#check S1804FirstMissing_iff_S1758
#check S1804FirstMissing_iff_sourceRetraction
#check S1804RecordedActual_iff_unit
#check S1804RecordedActual_iff_end
#check S1804StackEquivOfRecordedActual
#check S1804CounitData_of_recordedActual
#check S1804RecordedActual_of_counitData
#check S1804RecordedActual_iff_counitData
#check S1804End_eq_one_of_recordedActual
#check S1804FirstMissing_to_S1756FirstMissing
#check S1804FirstMissing_to_sourceRetraction
#check S1804FirstMissing_to_sourceRepresentableAll
#check S1804FirstMissing_iff_liftPointSurj

#print axioms S1804IsoCommaFiberEquiv
#print axioms S1804IsoCommaPullback_fiber
#print axioms S1804SourceSquare
#print axioms S1804SourceCone
#print axioms S1804Source_isPullback
#print axioms S1804SourceCone_proj
#print axioms S1804LiftIsoOfUnit
#print axioms S1804LiftEssSurjOfUnit
#print axioms S1804LiftEssSurj_iff_unit
#print axioms S1804LiftEssSurj_iff_end
#print axioms S1804UnitOfLiftConeIso
#print axioms S1804LiftConeIso_iff_unit
#print axioms S1804LiftEssSurj_iff_liftConeIso
#print axioms S1804FirstMissing_iff_S1756
#print axioms S1804FirstMissing_iff_S1758
#print axioms S1804FirstMissing_iff_sourceRetraction
#print axioms S1804RecordedActual_iff_unit
#print axioms S1804RecordedActual_iff_end
#print axioms S1804StackEquivOfRecordedActual
#print axioms S1804CounitData_of_recordedActual
#print axioms S1804RecordedActual_of_counitData
#print axioms S1804RecordedActual_iff_counitData
#print axioms S1804End_eq_one_of_recordedActual
#print axioms S1804FirstMissing_to_S1756FirstMissing
#print axioms S1804FirstMissing_to_sourceRetraction
#print axioms S1804FirstMissing_to_sourceRepresentableAll
#print axioms S1804FirstMissing_iff_liftPointSurj

end LeanFormal.IUT.XiFPaper.S1804IsoCommaPullbackActual
