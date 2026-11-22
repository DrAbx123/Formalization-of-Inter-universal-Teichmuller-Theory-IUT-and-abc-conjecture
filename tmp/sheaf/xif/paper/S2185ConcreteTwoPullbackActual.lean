import tmp.sheaf.xif.paper.S2130ExplicitD6Actual
import tmp.sheaf.xif.paper.S1911RepresentableTwoPullbackActual
import tmp.sheaf.xif.paper.S2028SourceSchemeActual
import tmp.sheaf.xif.paper.S2123PresentationConeESActual
import tmp.sheaf.xif.paper.S2071PastingWitnessActual
/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S2185
-/

/-!
# S2185: the concrete two-pullback comparison for the S2130 strict fibre product

## What is proved

For the S2130 strict fibre product

  S2130P f g T ptA = (B x_X T) x_{C x_X T} T,

we construct, for every cone c over the outer square

  B --g.map--> C <--ptC-- T,

the two presentation cones S2185ConePB and S2185ConePC, the strict square
S2185StrictSquare with apex S2130P, and the strict cone S2185StrictCone
from the comparison isomorphism S2185StrictConeIso.  The S1911 theorem then
produces the lift and its two comparison 2-cells.  The remaining witness fields
are subsingleton eliminations: into the representable targets T, C x_X T,
B x_X T for liftToX/liftTwoCell_toY/twoCell_ext, and into the thin cover fibre
B.source.fiber (S2028) for liftTwoCell_toX.

Consequently the file proves

  S2185ConcreteTwoPullback_of_strictConeIso :
      S2185StrictConeIso -> S2130ConcreteTwoPullback.

## The exact first missing

The only unproved input is S2185StrictConeIso: for every cone c of the outer
square, an isomorphism

  PB.isPullback.lift W c_PB ; y(Phi) ~= c.toY ; y(Graph)

of strong transformations into the representable stack y(C x_X T).  This is
the strict comparison of the two presentation lifts along the C-leg.  It is
not a field of EtaleStackBaseChangePresentation and is not a formal
consequence of the weak TwoPullbackWitness: the project records in S2100 and
S2123 that the corresponding full presentation property is not available for
arbitrary weak presentations (indeed S2094's uniform form is refuted).  This
file therefore does not assert S2185StrictConeIso; it records it as the exact
first missing statement and proves the target from it.

No sorry, no new axiom, no fabricated field or witness.
-/



noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2185ConcreteTwoPullbackActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1911RepresentableTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2042D6GeometricHalfActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2130ExplicitD6Actual
open LeanFormal.IUT.XiFPaper.S2028SourceSchemeActual
open LeanFormal.IUT.XiFPaper.S2123PresentationConeESActual
open LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual
open LeanFormal.IUT.XiFPaper.S2001LiftCommutesActual

universe u

abbrev S2185Y (S : SchemeOverField S1726K) : EtaleStackPseudofunctor S1726K :=
  schemeRepresentableEtalePseudofunctor S1726K S

abbrev S2185PBSquare {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber) :
    EtalePseudofunctorSquare (S2185Y (S2130PB f g T ptA).pullbackScheme)
      B.source.fiber (S2185Y T) S1726Orbicurve.stack.fiber :=
  EtalePseudofunctorSquare.mk (S2130PB f g T ptA).toSource
    (S2130PB f g T ptA).projectionMap.transformation B.map
    (S2130PtX f T ptA) (S2130PB f g T ptA).commutes

abbrev S2185PCSquare {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber) :
    EtalePseudofunctorSquare (S2185Y (S2130PC f T ptA).pullbackScheme)
      C.source.fiber (S2185Y T) S1726Orbicurve.stack.fiber :=
  EtalePseudofunctorSquare.mk (S2130PC f T ptA).toSource
    (S2130PC f T ptA).projectionMap.transformation C.map
    (S2130PtX f T ptA) (S2130PC f T ptA).commutes

theorem S2185SubsingletonRepresentable {W : EtaleStackPseudofunctor S1726K}
    {S : SchemeOverField S1726K} {f g : Pseudofunctor.StrongTrans W (S2185Y S)} :
    Subsingleton (f ⟶ g) :=
  Iut.EtalePseudofunctorSquare.subsingleton_strongTrans_schemeRepresentable

theorem S2185SubsingletonOrbicurve {W : EtaleStackPseudofunctor S1726K}
    {f g : Pseudofunctor.StrongTrans W S1726Orbicurve.stack.fiber} :
    Subsingleton (f ⟶ g) :=
  Iut.EtalePseudofunctorSquare.subsingleton_strongTrans_schemeRepresentable
    (S := S1726AffineOver)

noncomputable def S2185ConePB {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    (S2185PBSquare f g T ptA).Cone W where
  toX := c.toX
  toY := c.toY
  commutes :=
    (S2058WhiskerLeftIso c.toX B.map
      (Pseudofunctor.StrongTrans.vcomp g.map C.map) g.commutes.symm).trans
      ((S2058AssociatorIso c.toX g.map C.map).symm.trans
        ((S2058WhiskerRightIso
          (Pseudofunctor.StrongTrans.vcomp c.toX g.map)
          (Pseudofunctor.StrongTrans.vcomp c.toY (S2130PtC f T ptA))
          C.map c.commutes).trans
          (S2058AssociatorIso c.toY (S2130PtC f T ptA) C.map)))

noncomputable def S2185ConePC {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    (S2185PCSquare f g T ptA).Cone W where
  toX := Pseudofunctor.StrongTrans.vcomp c.toX g.map
  toY := c.toY
  commutes :=
    (S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp c.toX g.map)
      (Pseudofunctor.StrongTrans.vcomp c.toY (S2130PtC f T ptA))
      C.map c.commutes).trans
      (S2058AssociatorIso c.toY (S2130PtC f T ptA) C.map)

theorem S2185Val_strongTransOfHom {S U : SchemeOverField S1726K} (h : S ⟶ U)
    (U' : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : (S2185Y S).obj U') :
    S1911Val (S1742StrongTransOfHom h) U' a = a.as ≫ h := by
  rw [S1911Val_def]
  change ((S1742App h U').toFunctor.obj a).as = a.as ≫ h
  rw [← Discrete.mk_as a, S1742App_obj]

theorem S2185P_fst_Phi_eq {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber) :
    S2130P_fst f g T ptA ≫ S2130Phi f g T ptA =
      S2130P_snd f g T ptA ≫ S2130Graph f g T ptA := by
  apply Over.OverMorphism.ext
  exact Limits.pullback.condition

noncomputable def S2185StrictSquare_commutes {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (S2130P_fst f g T ptA))
        (S1742StrongTransOfHom (S2130Phi f g T ptA)))
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (S2130P_snd f g T ptA))
        (S1742StrongTransOfHom (S2130Graph f g T ptA))) := by
  classical
  exact (S1911Val_isoOfValEq (T := (S2130PC f T ptA).pullbackScheme)
    (L := Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (S2130P_fst f g T ptA))
      (S1742StrongTransOfHom (S2130Phi f g T ptA)))
    (L' := Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (S2130P_snd f g T ptA))
      (S1742StrongTransOfHom (S2130Graph f g T ptA)))
    (by
      intro U a
      rw [S1911Val_vcomp, S1911Val_vcomp]
      rw [S2185Val_strongTransOfHom, S2185Val_strongTransOfHom]
      rw [S1742HomOfStrongTrans_strongTransOfHom,
        S1742HomOfStrongTrans_strongTransOfHom]
      simp only [Category.assoc]
      rw [S2185P_fst_Phi_eq])).some

theorem S2185P_isPullback {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber) :
    IsPullback (S2130P_fst f g T ptA).left (S2130P_snd f g T ptA).left
      (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left := by
  change IsPullback
    (Limits.pullback.fst (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left)
    (Limits.pullback.snd (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left)
    (S2130Phi f g T ptA).left (S2130Graph f g T ptA).left
  exact IsPullback.of_hasPullback _ _

abbrev S2185StrictSquare {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber) :
    EtalePseudofunctorSquare (S2185Y (S2130P f g T ptA))
      (S2185Y (S2130PB f g T ptA).pullbackScheme)
      (S2185Y T)
      (S2185Y (S2130PC f T ptA).pullbackScheme) :=
  EtalePseudofunctorSquare.mk
    (S1742StrongTransOfHom (S2130P_fst f g T ptA))
    (S1742StrongTransOfHom (S2130P_snd f g T ptA))
    (S1742StrongTransOfHom (S2130Phi f g T ptA))
    (S1742StrongTransOfHom (S2130Graph f g T ptA))
    (S2185StrictSquare_commutes f g T ptA)

def S2185StrictConeIso : Prop :=
  forall (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    (W : EtaleStackPseudofunctor S1726K)
    (c : (S2130BaseSquare f g T ptA).Cone W),
    Nonempty
      (Iso
        (Pseudofunctor.StrongTrans.vcomp
          ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
          (S1742StrongTransOfHom (S2130Phi f g T ptA)))
        (Pseudofunctor.StrongTrans.vcomp c.toY
          (S1742StrongTransOfHom (S2130Graph f g T ptA))))

noncomputable def S2185StrictCone (h : S2185StrictConeIso)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    (S2185StrictSquare f g T ptA).Cone W where
  toX := (S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c)
  toY := c.toY
  commutes := (h A B C f g T ptA W c).some

noncomputable def S2185StrictWitness (h : S2185StrictConeIso)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber) :
    (S2185StrictSquare f g T ptA).TwoPullbackWitness :=
  S1911Witness (sq := S2185StrictSquare f g T ptA)
    (pX := S2130P_fst f g T ptA) (pY := S2130P_snd f g T ptA)
    (by
      simpa only [S1911BaseF, S1911BaseG,
        S1742HomOfStrongTrans_strongTransOfHom] using
        S2185P_isPullback f g T ptA)
    rfl rfl

noncomputable def S2185Lift (h : S2185StrictConeIso)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    (W : EtaleStackPseudofunctor S1726K)
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Pseudofunctor.StrongTrans W (S2185Y (S2130P f g T ptA)) :=
  (S2185StrictWitness h f g T ptA).lift W (S2185StrictCone h f g T ptA c)

noncomputable def S2185LiftToX (h : S2185StrictConeIso)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S2185Lift h f g T ptA W c)
        (S2130ToSource f g T ptA)) c.toX :=
  (S2058AssociatorIso (S2185Lift h f g T ptA W c)
    (S1742StrongTransOfHom (S2130P_fst f g T ptA))
    (S2130PB f g T ptA).toSource).symm.trans
    ((S2058WhiskerRightIso
      (Pseudofunctor.StrongTrans.vcomp (S2185Lift h f g T ptA W c)
        (S1742StrongTransOfHom (S2130P_fst f g T ptA)))
      ((S2130PB f g T ptA).isPullback.lift W (S2185ConePB f g T ptA c))
      (S2130PB f g T ptA).toSource
      ((S2185StrictWitness h f g T ptA).liftToX W
        (S2185StrictCone h f g T ptA c))).trans
      ((S2130PB f g T ptA).isPullback.liftToX W (S2185ConePB f g T ptA c)))

noncomputable def S2185LiftToY (h : S2185StrictConeIso)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2130BaseSquare f g T ptA).Cone W) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp (S2185Lift h f g T ptA W c)
        (S2130Proj f g T ptA)) c.toY :=
  (S2185StrictWitness h f g T ptA).liftToY W (S2185StrictCone h f g T ptA c)

noncomputable def S2185ConePBMorphism {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    (S2185PBSquare f g T ptA).ConeMorphism (S2185ConePB f g T ptA s)
      (S2185ConePB f g T ptA t) where
  toX := m.toX
  toY := m.toY
  compatibility := by
    exact @Subsingleton.elim _ (S2185SubsingletonOrbicurve
      (f := Pseudofunctor.StrongTrans.vcomp (S2185ConePB f g T ptA s).toX
        (S2185PBSquare f g T ptA).xToBase)
      (g := Pseudofunctor.StrongTrans.vcomp (S2185ConePB f g T ptA t).toY
        (S2185PBSquare f g T ptA).yToBase)) _ _

noncomputable def S2185ConeStrictMorphism (h : S2185StrictConeIso)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    (S2185StrictSquare f g T ptA).ConeMorphism (S2185StrictCone h f g T ptA s)
      (S2185StrictCone h f g T ptA t) where
  toX := (S2130PB f g T ptA).isPullback.liftTwoCell W
    (S2185ConePB f g T ptA s) (S2185ConePB f g T ptA t)
    (S2185ConePBMorphism f g T ptA m)
  toY := m.toY
  compatibility := by
    exact @Subsingleton.elim _ (S2185SubsingletonRepresentable
      (S := (S2130PC f T ptA).pullbackScheme)
      (f := Pseudofunctor.StrongTrans.vcomp (S2185StrictCone h f g T ptA s).toX
        (S2185StrictSquare f g T ptA).xToBase)
      (g := Pseudofunctor.StrongTrans.vcomp (S2185StrictCone h f g T ptA t).toY
        (S2185StrictSquare f g T ptA).yToBase)) _ _

noncomputable def S2185LiftTwoCell (h : S2185StrictConeIso)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    S2185Lift h f g T ptA W s ⟶ S2185Lift h f g T ptA W t :=
  (S2185StrictWitness h f g T ptA).liftTwoCell W
    (S2185StrictCone h f g T ptA s) (S2185StrictCone h f g T ptA t)
    (S2185ConeStrictMorphism h f g T ptA m)


theorem S2185Modification_subsingleton {C : S1728Cover}
    (hC : S2001CoverFiberDiscrete C)
    {W : EtaleStackPseudofunctor S1726K}
    {F G : Pseudofunctor.StrongTrans W C.source.fiber} :
    Subsingleton (F ⟶ G) := by
  constructor
  intro a b
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext x
  exact @Subsingleton.elim _
    (hC U ((F.app U).toFunctor.obj x) ((G.app U).toFunctor.obj x)) _ _

theorem S2185LiftTwoCell_toY (h : S2185StrictConeIso)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight (S2185LiftTwoCell h f g T ptA m)
        (S2130Proj f g T ptA) =
      (S2185LiftToY h f g T ptA s).hom ≫ m.toY ≫
        (S2185LiftToY h f g T ptA t).inv := by
  exact @Subsingleton.elim _
    (S2185SubsingletonRepresentable (S := T)
      (f := Pseudofunctor.StrongTrans.vcomp (S2185Lift h f g T ptA W s)
        (S2130Proj f g T ptA))
      (g := Pseudofunctor.StrongTrans.vcomp (S2185Lift h f g T ptA W t)
        (S2130Proj f g T ptA))) _ _

theorem S2185LiftTwoCell_toX (h : S2185StrictConeIso)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S2130BaseSquare f g T ptA).Cone W}
    (m : (S2130BaseSquare f g T ptA).ConeMorphism s t) :
    Pseudofunctor.StrongTrans.whiskerRight (S2185LiftTwoCell h f g T ptA m)
        (S2130ToSource f g T ptA) =
      (S2185LiftToX h f g T ptA s).hom ≫ m.toX ≫
        (S2185LiftToX h f g T ptA t).inv := by
  exact @Subsingleton.elim _
    (S2185Modification_subsingleton (C := B) (S2028CoverFiberDiscrete B)
      (F := Pseudofunctor.StrongTrans.vcomp
        (S2185Lift h f g T ptA W s) (S2130ToSource f g T ptA))
      (G := Pseudofunctor.StrongTrans.vcomp
        (S2185Lift h f g T ptA W t) (S2130ToSource f g T ptA))) _ _

theorem S2185TwoCell_ext (h : S2185StrictConeIso)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber)
    {W : EtaleStackPseudofunctor S1726K}
    {first second : Pseudofunctor.StrongTrans W (S2185Y (S2130P f g T ptA))}
    (alpha beta : first ⟶ second)
    (h1 : Pseudofunctor.StrongTrans.whiskerRight alpha (S2130ToSource f g T ptA) =
      Pseudofunctor.StrongTrans.whiskerRight beta (S2130ToSource f g T ptA))
    (h2 : Pseudofunctor.StrongTrans.whiskerRight alpha (S2130Proj f g T ptA) =
      Pseudofunctor.StrongTrans.whiskerRight beta (S2130Proj f g T ptA)) :
    alpha = beta := by
  exact @Subsingleton.elim _
    (S2185SubsingletonRepresentable (S := S2130P f g T ptA)
      (f := first) (g := second)) alpha beta

noncomputable def S2185TwoPullbackWitness (h : S2185StrictConeIso)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans (S2185Y T) A.source.fiber) :
    (S2130BaseSquare f g T ptA).TwoPullbackWitness where
  lift W c := S2185Lift h f g T ptA W c
  liftToX W c := S2185LiftToX h f g T ptA c
  liftToY W c := S2185LiftToY h f g T ptA c
  liftTwoCell W s t m := S2185LiftTwoCell h f g T ptA m
  liftTwoCell_toX W s t m := S2185LiftTwoCell_toX h f g T ptA m
  liftTwoCell_toY W s t m := S2185LiftTwoCell_toY h f g T ptA m
  twoCell_ext W first second alpha beta h1 h2 :=
    S2185TwoCell_ext h f g T ptA alpha beta h1 h2

noncomputable def S2185ConcreteTwoPullback_of_strictConeIso (h : S2185StrictConeIso) :
    S2130ConcreteTwoPullback := by
  intro A B C f g T ptA
  exact S2185TwoPullbackWitness h f g T ptA


def S2185FirstMissing : Prop := S2185StrictConeIso

noncomputable def S2185ConcreteTwoPullback_of_firstMissing
    (h : S2185FirstMissing) : S2130ConcreteTwoPullback :=
  S2185ConcreteTwoPullback_of_strictConeIso h

#print axioms S2185ConcreteTwoPullback_of_strictConeIso
#print axioms S2185ConcreteTwoPullback_of_firstMissing
#print axioms S2185Lift
#print axioms S2185LiftToX
#print axioms S2185LiftToY
#print axioms S2185TwoPullbackWitness

end LeanFormal.IUT.XiFPaper.S2185ConcreteTwoPullbackActual