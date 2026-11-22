/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors / S2023
-/
import tmp.sheaf.xif.paper.S2018IdentityRepairActual
import tmp.sheaf.xif.paper.S1844PointSeparatedActual

/-!
# S2023: the represented-source transport is proved; the residual is geometric

## What S2018 left open

S2018 reduced the corrected identity repair S2015IdentityRepairAll to the
conjunction S2018FirstMissing = S2018SourceSchemeAll AND S2018RepresentedSourceTransport.
The first conjunct is geometric: every finite-etale cover source must be
quasi-equivalent to the representable stack y Q of a scheme Q.  The second is the
bicategorical transport: such a representation must upgrade to a corrected
identity-point presentation.  S2018 records the transport as blocked, because the
recorded weak two-pullback witness has comparison 2-cells liftTwoCell_toX whose
target is the cover source, which is not discrete, so S1844SubsingletonMod cannot
discharge them; S1900SourceTransport and S1871StrongTransfer record the same
obstruction.

## The decisive structural fact

The S1726 orbicurve is literally the representable etale stack of its affine model
Spec R' (S1726Orbicurve_stack_fiber is rfl), and the canonical identity point is
literally the identity 1-cell of y (Spec R') (S1733BasePoint is rfl the identity).
Consequences, recorded at the start of this file:

* S2023OrbicurveStackFiber, S2023BasePoint_eq_id;
* the composite e.hom ; M of a source quasi-equivalence with the structure map
  lands in a representable stack, so its 2-Yoneda evaluation is an honest scheme
  morphism S2023Projection : Q -> Spec R', and 2-Yoneda produces the
  2-commutativity S2023Commutes of the transport square unconditionally.  The
  point condition that S2018 isolated is therefore not an obstruction at all;
* the remaining input is exactly the weak-witness coherence equation on the source
  side, and that is a coherence theorem of the ambient bicategory.

## What is proved here

1. S2023Beta, S2023Beta_natural (Section 1): in an arbitrary bicategory the
   comparison (u ; k) ; h ~ u attached to k ; h ~ id is natural in u.  This is
   exactly liftTwoCell_toX, proved by the exchange law and the unitors, with no
   discreteness hypothesis on the target.

   S2023Cancel: cancellation of a quasi-equivalence on the right, from the
   triangle identity h ; k ~ id.

2. S2023Witness (Section 3): the full seven-field weak two-pullback witness of the
   transport square, for every stack morphism M : X -> y (Spec R') and every
   quasi-equivalence e : y Q ~ X.  The lift is c.toX ; e.inv; liftTwoCell_toY and
   2-cell extensionality are 2-cell uniqueness into the representable stacks
   y (Spec R') and y Q (S1844).

3. S2023Full (Section 3): the corrected full 2-dimensional property of the same
   square, from the triangle identities alone.

4. S2023Presentation (Section 4) and the transport theorem
   S2023RepresentedSourceTransport (Section 5).  The finite-etale field of a cover
   is never used, so the theorem holds for every stack morphism into the orbicurve.

5. Consequences (Section 5):

     S2018FirstMissing        <->  S2018SourceSchemeAll,
     S2015IdentityRepairAll   <->  S2018SourceSchemeAll,

   hence S2018SourceSchemeAll alone yields S2015IdentityRepairAll and
   S2001UniqFirstMissing, and the transport half of S2018FirstMissing is settled.

## Honest boundary

S2018SourceSchemeAll is NOT proved here, and no counterexample to it is
constructed: it is the exact residual.  The recorded finite-etale condition on a
cover is only the weak representable base-change condition, which does not bound
the source stack, so nothing in the tree forces the source to be a scheme; a finite
etale gerbe over Spec R' would be a counterexample in the geometric semantics, but
no such cover is constructed here.  Neither direction of S2018SourceSchemeAll is
claimed.

No sorry, no new axiom, no fake 2-cell, no fake equivalence, no
Shrink/ULift/PUnit and no change of the target.  Axiom footprint: propext,
Classical.choice, Quot.sound (audit block at the end).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2023SourceSchemeActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1804IsoCommaPullbackActual
open LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1900StrongSliceRealizationActual
open LeanFormal.IUT.XiFPaper.S2001LiftCommutesActual
open LeanFormal.IUT.XiFPaper.S2010BaseChangeFullActual
open LeanFormal.IUT.XiFPaper.S2015FullPullbackActual
open LeanFormal.IUT.XiFPaper.S2018IdentityRepairActual

/-! ## 0. The orbicurve stack is the representable stack of the base -/

/-- The stack of the S1726 D6 orbicurve is the representable etale stack of its
affine model Spec R'.  This is a definitional identity, not an equivalence. -/
theorem S2023OrbicurveStackFiber :
    S1726Orbicurve.stack.fiber = S1743Y S1726AffineOver := rfl

/-- The canonical identity point of the orbicurve is the identity 1-cell of the
representable stack of Spec R'. -/
theorem S2023BasePoint_eq_id :
    S1733BasePoint = Pseudofunctor.StrongTrans.id (S1743Y S1726AffineOver) := rfl

/-- Every cover map lands in the representable stack of Spec R'. -/
theorem S2023OrbicurveFiberRep :
    S1726Orbicurve.stack.fiber =
      schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver := rfl

/-! ## 1. The naturality of the unit comparison in an arbitrary bicategory -/

universe uB vB wB

section BicategoryCoherence

variable {B : Type uB} [CategoryTheory.Bicategory.{vB, wB} B]

/-- The comparison 2-isomorphism (u ; k) ; h ~ u attached to a 2-isomorphism
k ; h ~ id.  This is the 2-cell liftToX of the transport weak witness. -/
noncomputable def S2023Beta {a X P : B} (u : a ⟶ X) (k : X ⟶ P) (h : P ⟶ X)
    (e : k ≫ h ≅ 𝟙 X) : (u ≫ k) ≫ h ≅ u :=
  (CategoryTheory.Bicategory.associator u k h) ≪≫
    (CategoryTheory.Bicategory.whiskerLeftIso u e) ≪≫
      (CategoryTheory.Bicategory.rightUnitor u)

/-- **Naturality of the unit comparison.**  For every 2-cell m : u1 ~ u2 the
whiskering (m ▷ k) ▷ h is the conjugation of m by S2023Beta.  This is precisely the
coherence equation liftTwoCell_toX of a two-pullback witness whose source side
carries a quasi-equivalence k ; h ~ id; it holds in any bicategory, with no
discreteness hypothesis on the target. -/
theorem S2023Beta_natural {a X P : B} (u₁ u₂ : a ⟶ X) (m : u₁ ⟶ u₂)
    (k : X ⟶ P) (h : P ⟶ X) (e : k ≫ h ≅ 𝟙 X) :
    (m ▷ k) ▷ h = (S2023Beta u₁ k h e).hom ≫ m ≫ (S2023Beta u₂ k h e).inv := by
  have h1 : (m ▷ k) ▷ h =
      (α_ u₁ k h).hom ≫ (m ▷ (k ≫ h)) ≫ (α_ u₂ k h).inv :=
    CategoryTheory.Bicategory.whiskerRight_comp_symm m k h
  have hex : (u₁ ◁ e.hom) ≫ (m ▷ 𝟙 X) = (m ▷ (k ≫ h)) ≫ (u₂ ◁ e.hom) :=
    CategoryTheory.Bicategory.whisker_exchange m e.hom
  have hwit : (m ▷ 𝟙 X) = (ρ_ u₁).hom ≫ m ≫ (ρ_ u₂).inv :=
    CategoryTheory.Bicategory.whiskerRight_id m
  have hkey : (u₁ ◁ e.hom) ≫ (ρ_ u₁).hom ≫ m ≫ (ρ_ u₂).inv =
      (m ▷ (k ≫ h)) ≫ (u₂ ◁ e.hom) := by
    rw [← hwit, hex]
  have hm' : ((u₁ ◁ e.hom) ≫ (ρ_ u₁).hom ≫ m ≫ (ρ_ u₂).inv) ≫ (u₂ ◁ e.inv) =
      (m ▷ (k ≫ h)) := by
    rw [hkey, Category.assoc, ← CategoryTheory.Bicategory.whiskerLeft_comp,
      e.hom_inv_id, CategoryTheory.Bicategory.whiskerLeft_id, Category.comp_id]
  have hm : (m ▷ (k ≫ h)) =
      (u₁ ◁ e.hom) ≫ (ρ_ u₁).hom ≫ m ≫ (ρ_ u₂).inv ≫ (u₂ ◁ e.inv) := by
    rw [hm'.symm]
    simp only [Category.assoc]
  rw [h1, hm]
  simp only [S2023Beta, Iso.trans_hom, Iso.trans_inv,
    CategoryTheory.Bicategory.whiskerLeftIso_hom,
    CategoryTheory.Bicategory.whiskerLeftIso_inv, Category.assoc]

/-- Cancellation of a quasi-equivalence on the right: a 2-isomorphism of the
composites with h promotes to a 2-isomorphism of the 1-cells.  Only the triangle
identity h ; k ~ id is used. -/
theorem S2023Cancel {a P X : B} (h : P ⟶ X) (k : X ⟶ P) (η : h ≫ k ≅ 𝟙 P)
    (u v : a ⟶ P) (α : u ≫ h ≅ v ≫ h) : Nonempty (u ≅ v) :=
  ⟨(CategoryTheory.Bicategory.rightUnitor u).symm ≪≫
    (CategoryTheory.Bicategory.whiskerLeftIso u η.symm) ≪≫
      (CategoryTheory.Bicategory.associator u h k).symm ≪≫
        (CategoryTheory.Bicategory.whiskerRightIso α k) ≪≫
          (CategoryTheory.Bicategory.associator v h k) ≪≫
            (CategoryTheory.Bicategory.whiskerLeftIso v η) ≪≫
              (CategoryTheory.Bicategory.rightUnitor v)⟩

end BicategoryCoherence

/-! ## 1b. The same lemmas in the ambient bicategory of etale stacks -/

/-- The unit comparison in the bicategory of etale stacks over S1726K. -/
noncomputable def S2023BetaStack {a X P : EtaleStackPseudofunctor S1726K}
    (u : a ⟶ X) (k : X ⟶ P) (h : P ⟶ X) (e : k ≫ h ≅ 𝟙 X) :
    (u ≫ k) ≫ h ≅ u :=
  S2023Beta (B := EtaleStackPseudofunctor S1726K) u k h e

/-- Naturality of the unit comparison in the bicategory of etale stacks. -/
theorem S2023BetaStack_natural {a X P : EtaleStackPseudofunctor S1726K}
    (u₁ u₂ : a ⟶ X) (m : u₁ ⟶ u₂) (k : X ⟶ P) (h : P ⟶ X) (e : k ≫ h ≅ 𝟙 X) :
    (m ▷ k) ▷ h = (S2023BetaStack u₁ k h e).hom ≫ m ≫ (S2023BetaStack u₂ k h e).inv :=
  S2023Beta_natural (B := EtaleStackPseudofunctor S1726K) u₁ u₂ m k h e

/-- Right cancellation of a quasi-equivalence in the bicategory of etale stacks. -/
theorem S2023CancelStack {a P X : EtaleStackPseudofunctor S1726K}
    (h : P ⟶ X) (k : X ⟶ P) (η : h ≫ k ≅ 𝟙 P)
    (u v : a ⟶ P) (α : u ≫ h ≅ v ≫ h) : Nonempty (u ≅ v) :=
  S2023Cancel (B := EtaleStackPseudofunctor S1726K) h k η u v α


/-! ## 2. The transport square of a represented source -/

section Transport

variable (X : EtaleStackOverField S1726K)
variable (M : X.Hom S1726Orbicurve.stack)
variable (Q : SchemeOverField S1726K)
variable (e : S1756StackEquiv (S1743Y Q) X.fiber)

/-- The transported structure map: the composite of the quasi-equivalence with the
structure map, read as a 1-cell into the representable stack of Spec R'. -/
noncomputable def S2023TransportMap :
    Pseudofunctor.StrongTrans (S1743Y Q) (S1743Y S1726AffineOver) :=
  Pseudofunctor.StrongTrans.vcomp e.hom M

/-- The transported map lands in a representable stack, so its 2-Yoneda evaluation
is an actual scheme morphism Q -> Spec R'. -/
noncomputable def S2023Projection : Q ⟶ S1726AffineOver :=
  S1743YonedaEval Q S1726AffineOver (S2023TransportMap X M Q e)

/-- The defining equation of the projection. -/
theorem S2023Projection_def :
    S2023Projection X M Q e =
      S1743YonedaEval Q S1726AffineOver (S2023TransportMap X M Q e) := rfl

/-- The representable 1-cell of the projection. -/
noncomputable def S2023Map :
    Pseudofunctor.StrongTrans (S1743Y Q) (S1743Y S1726AffineOver) :=
  S1743StrongTransOfHom (S2023Projection X M Q e)

/-- Its 2-Yoneda evaluation is the projection itself. -/
theorem S2023Eval_map :
    S1743YonedaEval Q S1726AffineOver (S2023Map X M Q e) =
      S2023Projection X M Q e :=
  S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) (S2023Projection X M Q e)

/-- **2-Yoneda identifies the transported map with its representable form.**  This
is the point condition that S2018 recorded as obstructed; on the representable target
y (Spec R') it is exactly the 2-Yoneda round trip. -/
noncomputable def S2023MapInv :
    Iso (S2023Map X M Q e) (S2023TransportMap X M Q e) :=
  S1742StrongTransIsoOfHom (F := S1726K) (S := Q) (T := S1726AffineOver)
    (S2023TransportMap X M Q e)

/-- The 2-isomorphism in the forward direction. -/
noncomputable def S2023MapIso :
    Iso (S2023TransportMap X M Q e) (S2023Map X M Q e) :=
  (S2023MapInv X M Q e).symm

/-- The representability datum of the projection. -/
noncomputable def S2023ProjectionMap :
    SchemeRepresentableMap (S2023Projection X M Q e) :=
  S1743SchemeRepresentableMap (S2023Projection X M Q e)

/-- The 2-commutativity of the transport square.  Its right leg is the identity
point, so the right unitor closes the gap. -/
noncomputable def S2023Commutes :
    Iso (S2023TransportMap X M Q e)
      (Pseudofunctor.StrongTrans.vcomp
        (S2023ProjectionMap X M Q e).transformation S1733BasePoint) :=
  (S2023MapIso X M Q e) ≪≫ (S1756RightUnitorIso (S2023Map X M Q e)).symm

/-- The transport square: apex y Q, comparison to the source e.hom, and the
representable map of the transported structure map as the base leg. -/
noncomputable def S2023Square :
    EtalePseudofunctorSquare (S1743Y Q) X.fiber
      (S1743Y S1726AffineOver) S1726Orbicurve.stack.fiber :=
  EtalePseudofunctorSquare.mk e.hom
    (S2023ProjectionMap X M Q e).transformation M S1733BasePoint
    (S2023Commutes X M Q e)

/-- The lift of a pseudo-cone along the quasi-equivalence. -/
noncomputable def S2023Lift (W : EtaleStackPseudofunctor S1726K)
    (c : (S2023Square X M Q e).Cone W) :
    Pseudofunctor.StrongTrans W (S1743Y Q) :=
  Pseudofunctor.StrongTrans.vcomp c.toX e.inv

/-- The first comparison 2-isomorphism: the unit comparison of the
quasi-equivalence.  This is the 2-cell S2018 recorded as blocked. -/
noncomputable def S2023LiftToX (W : EtaleStackPseudofunctor S1726K)
    (c : (S2023Square X M Q e).Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2023Lift X M Q e W c)
      (S2023Square X M Q e).toX) c.toX :=
  S2023BetaStack c.toX e.inv e.hom e.counit

/-- The second comparison 2-isomorphism: transport along the quasi-equivalence and
the 2-Yoneda identification of the structure map. -/
noncomputable def S2023LiftToY (W : EtaleStackPseudofunctor S1726K)
    (c : (S2023Square X M Q e).Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2023Lift X M Q e W c)
      (S2023Square X M Q e).toY) c.toY :=
  (S1756AssociatorIso c.toX e.inv (S2023Map X M Q e)) ≪≫
    (S1756WhiskerLeftIso c.toX
      (Pseudofunctor.StrongTrans.vcomp e.inv (S2023Map X M Q e))
      (Pseudofunctor.StrongTrans.vcomp e.inv (S2023TransportMap X M Q e))
      (S1756WhiskerLeftIso e.inv (S2023Map X M Q e) (S2023TransportMap X M Q e)
        (S2023MapInv X M Q e))) ≪≫
      (S1756WhiskerLeftIso c.toX
        (Pseudofunctor.StrongTrans.vcomp e.inv (S2023TransportMap X M Q e))
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp e.inv e.hom) M)
        (S1756AssociatorIso e.inv e.hom M).symm) ≪≫
        (S1756WhiskerLeftIso c.toX
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.vcomp e.inv e.hom) M)
          (Pseudofunctor.StrongTrans.vcomp
            (Pseudofunctor.StrongTrans.id X.fiber) M)
          (S1756WhiskerRightIso (Pseudofunctor.StrongTrans.vcomp e.inv e.hom)
            (Pseudofunctor.StrongTrans.id X.fiber) M e.counit)) ≪≫
          (S1756WhiskerLeftIso c.toX
            (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.id X.fiber) M) M
            (S1756LeftUnitorIso M)) ≪≫
            (c.commutes ≪≫ (S1756RightUnitorIso c.toY))

end Transport

/-! ## 3. The weak two-pullback witness and the full property -/

section Transport

variable (X : EtaleStackOverField S1726K)
variable (M : X.Hom S1726Orbicurve.stack)
variable (Q : SchemeOverField S1726K)
variable (e : S1756StackEquiv (S1743Y Q) X.fiber)

/-- **The seven-field weak two-pullback witness of the transport square.**  The two
source-side coherence equations are: the naturality of the unit comparison
(S2023BetaStack_natural), and 2-cell uniqueness into the representable stack
y (Spec R') (S1844).  The latter is legitimate here because the *first* leg is the
quasi-equivalence: the missing equation of S2018 was on the source side, and that is
exactly where the bicategory coherence theorem applies. -/
noncomputable def S2023Witness : (S2023Square X M Q e).TwoPullbackWitness where
  lift := fun W c => S2023Lift X M Q e W c
  liftToX := fun W c => S2023LiftToX X M Q e W c
  liftToY := fun W c => S2023LiftToY X M Q e W c
  liftTwoCell := fun W s t m =>
    Pseudofunctor.StrongTrans.whiskerRight m.toX e.inv
  liftTwoCell_toX := fun W s t m =>
    S2023BetaStack_natural s.toX t.toX m.toX e.inv e.hom e.counit
  liftTwoCell_toY := fun W s t m => (S1844SubsingletonMod _ _).allEq _ _
  twoCell_ext := fun W first second alpha beta _ _ =>
    (S1844SubsingletonMod first second).allEq alpha beta

/-- **The corrected full property of the transport square.** -/
theorem S2023Full : S2015FullPullback (S2023Square X M Q e) where
  exists_lift := fun W c =>
    ⟨S2023Lift X M Q e W c, ⟨S2023LiftToX X M Q e W c⟩,
      ⟨S2023LiftToY X M Q e W c⟩⟩
  unique_lift := fun W c f g h1 h2 h3 h4 =>
    S2023CancelStack e.hom e.inv e.unit f g
      ((Classical.choice h1) ≪≫ (Classical.choice h3).symm)

end Transport

/-! ## 4. The corrected identity-point presentation of a represented source -/

section Transport

variable (X : EtaleStackOverField S1726K)
variable (M : X.Hom S1726Orbicurve.stack)
variable (Q : SchemeOverField S1726K)
variable (e : S1756StackEquiv (S1743Y Q) X.fiber)

/-- **The transport presentation.**  A quasi-equivalence of y Q with the source of a
stack morphism M into the orbicurve produces a corrected base-change presentation of
M at the identity point with apex Q, with the full 2-dimensional universal property. -/
noncomputable def S2023Presentation :
    S2015FullBaseChangePresentation M S1726AffineOver S1733BasePoint where
  pullbackScheme := Q
  projection := S2023Projection X M Q e
  projectionMap := S2023ProjectionMap X M Q e
  toSource := e.hom
  commutes := S2023Commutes X M Q e
  isPullback := S2023Witness X M Q e
  isFull := S2023Full X M Q e

end Transport


/-! ## 5. The transport theorem -/

/-- **The represented-source transport, in the general form.**  For *every* stack
morphism M : X -> y (Spec R') into the orbicurve and *every* quasi-equivalence of
the representable stack of a scheme Q with the source X, there is a corrected
identity-point presentation of M with apex Q.  No finite-etale hypothesis on M is
used: the transport is purely bicategorical. -/
theorem S2023Transport_general (X : EtaleStackOverField S1726K)
    (M : X.Hom S1726Orbicurve.stack) (Q : SchemeOverField S1726K)
    (e : S1756StackEquiv (S1743Y Q) X.fiber) :
    Nonempty (S2015FullBaseChangePresentation M S1726AffineOver S1733BasePoint) :=
  ⟨S2023Presentation X M Q e⟩

/-- **S2018RepresentedSourceTransport holds.**  This is the second conjunct of
S2018FirstMissing, the half that S2018/S1900/S1871 recorded as blocked because the
weak witness needs a 2-cell equation into the non-discrete cover source. -/
theorem S2023RepresentedSourceTransport : S2018RepresentedSourceTransport := by
  intro C Q hQ
  obtain ⟨e⟩ := hQ
  exact S2023Transport_general C.source C.map Q e

/-- A single cover with a representable source already has the corrected
identity-point presentation. -/
theorem S2023IdentityRepair_of_sourceScheme (C : S1728Cover)
    (h : S2018SourceScheme C) : S2015IdentityRepair C := by
  obtain ⟨Q, ⟨e⟩⟩ := h
  exact S2023Transport_general C.source C.map Q e

/-! ## 6. The exact residual after S2023 -/

/-- **The residual is geometric alone.**  The corrected identity repair for all
covers is now *equivalent* to the single statement that every finite-etale cover
source is representable by a scheme. -/
theorem S2023FirstMissing_iff_sourceSchemeAll :
    S2018FirstMissing ↔ S2018SourceSchemeAll := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, S2023RepresentedSourceTransport⟩

/-- **The exact residual.**  S2018SourceSchemeAll is equivalent to the whole
corrected first missing statement. -/
theorem S2023Residual_iff_sourceSchemeAll :
    S2015IdentityRepairAll ↔ S2018SourceSchemeAll :=
  S2018IdentityRepairAll_iff_firstMissing.trans S2023FirstMissing_iff_sourceSchemeAll

/-- Source representability gives the corrected identity repair uniformly. -/
theorem S2023IdentityRepairAll_of_sourceSchemeAll (h : S2018SourceSchemeAll) :
    S2015IdentityRepairAll :=
  S2023Residual_iff_sourceSchemeAll.mpr h

/-- Source representability gives the first missing statement of S2018. -/
theorem S2023FirstMissing_of_sourceSchemeAll (h : S2018SourceSchemeAll) :
    S2018FirstMissing :=
  S2023FirstMissing_iff_sourceSchemeAll.mpr h

/-- Every cover whose source is representable has discrete geometric fibres. -/
theorem S2023CoverFiberDiscrete_of_sourceScheme (C : S1728Cover)
    (h : S2018SourceScheme C) : S2001CoverFiberDiscrete C := by
  obtain ⟨P⟩ := S2023IdentityRepair_of_sourceScheme C h
  exact S2015CoverFiberDiscrete_of_identityRepair C P

/-- Consequently S2018SourceSchemeAll already yields the S2001 target. -/
theorem S2023UniqFirstMissing_of_sourceSchemeAll (h : S2018SourceSchemeAll) :
    S2001UniqFirstMissing :=
  S2015UniqFirstMissing_of_identityRepairAll
    (S2023IdentityRepairAll_of_sourceSchemeAll h)

/-! ### What is known about the residual statement S2018SourceSchemeAll -/

/-- The identity quasi-equivalence of a stack with itself. -/
noncomputable def S2023StackEquivRefl (P : EtaleStackPseudofunctor S1726K) :
    S1756StackEquiv P P where
  hom := Pseudofunctor.StrongTrans.id P
  inv := Pseudofunctor.StrongTrans.id P
  unit := S1756RightUnitorIso (Pseudofunctor.StrongTrans.id P)
  counit := S1756RightUnitorIso (Pseudofunctor.StrongTrans.id P)

/-- A cover whose source is literally the representable stack of a scheme has a
representable source. -/
theorem S2023SourceScheme_of_representable (C : S1728Cover)
    (Q : SchemeOverField S1726K) (h : C.source.fiber = S1743Y Q) :
    S2018SourceScheme C :=
  ⟨Q, ⟨h ▸ S2023StackEquivRefl (S1743Y Q)⟩⟩

/-- In particular every cover whose source is the orbicurve stack itself is
representable.  The covers used in the tree (the terminal cover, S1850's doubled
cover and S2010's counterexample cover) all have the orbicurve as source. -/
theorem S2023SourceScheme_of_orbicurveSource (C : S1728Cover)
    (h : C.source.fiber = S1743Y S1726AffineOver) : S2018SourceScheme C :=
  S2023SourceScheme_of_representable C S1726AffineOver h

/-- The terminal cover has a representable source. -/
theorem S2023SourceScheme_terminal : S2018SourceScheme S1762TerminalCover :=
  S2023SourceScheme_of_orbicurveSource S1762TerminalCover rfl

/-- S1850's doubled cover has a representable source. -/
theorem S2023SourceScheme_doubled : S2018SourceScheme S1850DoubledCover :=
  S2023SourceScheme_of_orbicurveSource S1850DoubledCover rfl

/-- S2010's counterexample cover has a representable source. -/
theorem S2023SourceScheme_counterexample : S2018SourceScheme S2010CounterCover :=
  S2023SourceScheme_of_orbicurveSource S2010CounterCover rfl

/-- Consequently the corrected identity repair holds for every cover whose source
is the orbicurve stack. -/
theorem S2023IdentityRepair_orbicurveSource (C : S1728Cover)
    (h : C.source.fiber = S1743Y S1726AffineOver) : S2015IdentityRepair C :=
  S2023IdentityRepair_of_sourceScheme C (S2023SourceScheme_of_orbicurveSource C h)

/-- The three covers of the tree, through the uniform statement. -/
theorem S2023IdentityRepair_counterexample' : S2015IdentityRepair S2010CounterCover :=
  S2023IdentityRepair_of_sourceScheme S2010CounterCover S2023SourceScheme_counterexample

/-! ## 7. Honest boundary of S2018SourceSchemeAll

S2018SourceSchemeAll is not proved and not refuted in this file.  What is recorded is

* the residual is *exactly* this geometric statement (S2023Residual_iff_sourceSchemeAll);
* its finite-etale hypothesis on the cover is the weak representable base-change
  condition only, so it does not constrain the source stack.  In the geometric
  semantics a finite etale gerbe over Spec R' (for instance the classifying stack of
  Z/2) is a finite etale cover whose source is not a scheme, which is why the
  statement is not expected to follow from the definitions.  No such cover is
  constructed in this tree, and the three covers used here all have the orbicurve as
  source, so no counterexample is available either.  Both directions remain open. -/
/-- The residual statement, recorded as a named proposition for the queue. -/
def S2023FirstMissing : Prop := S2018SourceSchemeAll

/-- Its exact content for the corrected identity repair. -/
theorem S2023FirstMissing_iff : S2023FirstMissing ↔ S2015IdentityRepairAll :=
  S2023Residual_iff_sourceSchemeAll.symm


/-! ## 8. Checks and axiom audit -/

#check S2023OrbicurveStackFiber
#check S2023BasePoint_eq_id
#check @S2023Beta
#check @S2023Beta_natural
#check @S2023Cancel
#check S2023BetaStack
#check S2023BetaStack_natural
#check S2023CancelStack
#check S2023TransportMap
#check S2023Projection
#check S2023Map
#check S2023MapInv
#check S2023Commutes
#check S2023Square
#check S2023Lift
#check S2023LiftToX
#check S2023LiftToY
#check S2023Witness
#check S2023Full
#check S2023Presentation
#check S2023Transport_general
#check S2023RepresentedSourceTransport
#check S2023IdentityRepair_of_sourceScheme
#check S2023FirstMissing_iff_sourceSchemeAll
#check S2023Residual_iff_sourceSchemeAll
#check S2023IdentityRepairAll_of_sourceSchemeAll
#check S2023FirstMissing_of_sourceSchemeAll
#check S2023CoverFiberDiscrete_of_sourceScheme
#check S2023UniqFirstMissing_of_sourceSchemeAll
#check S2023StackEquivRefl
#check S2023SourceScheme_of_representable
#check S2023SourceScheme_of_orbicurveSource
#check S2023SourceScheme_terminal
#check S2023SourceScheme_doubled
#check S2023SourceScheme_counterexample
#check S2023IdentityRepair_orbicurveSource
#check S2023FirstMissing
#check S2023FirstMissing_iff

#print axioms S2023Beta
#print axioms S2023Beta_natural
#print axioms S2023Cancel
#print axioms S2023BetaStack_natural
#print axioms S2023MapInv
#print axioms S2023Commutes
#print axioms S2023Witness
#print axioms S2023Full
#print axioms S2023Presentation
#print axioms S2023Transport_general
#print axioms S2023RepresentedSourceTransport
#print axioms S2023IdentityRepair_of_sourceScheme
#print axioms S2023FirstMissing_iff_sourceSchemeAll
#print axioms S2023Residual_iff_sourceSchemeAll
#print axioms S2023IdentityRepairAll_of_sourceSchemeAll
#print axioms S2023CoverFiberDiscrete_of_sourceScheme
#print axioms S2023UniqFirstMissing_of_sourceSchemeAll
#print axioms S2023StackEquivRefl
#print axioms S2023SourceScheme_of_representable
#print axioms S2023SourceScheme_of_orbicurveSource
#print axioms S2023SourceScheme_terminal
#print axioms S2023SourceScheme_doubled
#print axioms S2023SourceScheme_counterexample
#print axioms S2023IdentityRepair_orbicurveSource
#print axioms S2023FirstMissing_iff

end LeanFormal.IUT.XiFPaper.S2023SourceSchemeActual
