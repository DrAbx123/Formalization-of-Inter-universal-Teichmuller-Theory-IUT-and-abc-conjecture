/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1943
-/
import tmp.sheaf.xif.paper.S1911RepresentableTwoPullbackActual

/-!
# S1943: assembling S1878EssSurj from the representable two-pullback theorem

S1911 proved the corrected two-pullback theorem for representable etale stacks
(S1911RepresentableTwoPullbackPullbackSquare) and refuted the literal S1897
statement (S1911_not_representableTwoPullback).  S1897 had reduced
S1878EssSurj to the extension datum S1897ExtensionData C, whose only
substantive field is a strong finite-etale structure on the extension map

    S1897ExtMap C = y(S1897CoverOver C) : y(C.carrier) -> y(Spec R'),

together with the *literal* identification of its identity-point presentation
with the triangle presentation.

This file performs the remaining assembly, and does so **without** that literal
identification.  The two halves are:

* **(a) The strong structure.**  For every finite etale cover C of Spec R'
  and every test scheme T with a scheme-valued point q of the orbicurve
  stack, the point is, by 2-Yoneda (S1742), 2-isomorphic to the Yoneda image of
  an actual scheme morphism q~ : T -> Spec R'.  Taking the fibre product of
  S1897CoverOver C and q~ in Over (Spec F') gives a scheme pullback square;
  S1911 turns it into a TwoPullbackWitness together with the full 2-universal
  property (S1852's S1852ConeEssSurj).  Transporting along the 2-isomorphism
  y(q~) ~= q produces the strong base-change presentation at the arbitrary
  point q.  Finiteness and etaleness of the projection are
  FiniteEtaleCover.finiteEtale_pullback.

* **(b) The model.**  The coherent cover is built from the strong structure by
  CoherentCover.ofStrong.  Its identity-point projection is the second leg of
  the fibre product of C -> Spec R' with the *identity*, hence the scheme C
  itself up to the canonical isomorphism pullback f 1 ~= X; Over.isoMk of that
  isomorphism gives S1816Obj A ~= C and therefore S1878EssSurj.

No sorry, no new axiom, no fake 2-cell and no fake isomorphism: every 2-cell is
built from actual scheme morphisms and pullback uniqueness.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1943AssembleEssSurjActual

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual
open LeanFormal.IUT.XiFPaper.S1897CoherentEssSurjActual
open LeanFormal.IUT.XiFPaper.S1911RepresentableTwoPullbackActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-! ## 1. The fibre product of the cover with a scheme-valued point -/

variable (C : S1816Target)

/-- The fibre product, as a scheme over Spec F'.  Its structure morphism is the
composite of the first projection with the structure morphism of the cover; the
second projection is a morphism over Spec F' because the square of structure
morphisms commutes. -/
noncomputable def S1943PbOver (T : SchemeOverField S1726K) (g : T ⟶ S1726AffineOver) :
    SchemeOverField S1726K :=
  Over.mk (Limits.pullback.fst (f := (S1897CoverOver C).left) (g := g.left) ≫
    (S1897CoverScheme C).hom)

/-- The first projection of the fibre product. -/
noncomputable def S1943PbFst (T : SchemeOverField S1726K) (g : T ⟶ S1726AffineOver) :
    S1943PbOver C T g ⟶ S1897CoverScheme C :=
  Over.homMk (Limits.pullback.fst (f := (S1897CoverOver C).left) (g := g.left)) rfl

/-- The second projection of the fibre product. -/
noncomputable def S1943PbSnd (T : SchemeOverField S1726K) (g : T ⟶ S1726AffineOver) :
    S1943PbOver C T g ⟶ T :=
  Over.homMk (Limits.pullback.snd (f := (S1897CoverOver C).left) (g := g.left)) (by
    show Limits.pullback.snd (f := (S1897CoverOver C).left) (g := g.left) ≫ T.hom =
      Limits.pullback.fst (f := (S1897CoverOver C).left) (g := g.left) ≫
        (S1897CoverScheme C).hom
    rw [← g.w, ← Category.assoc, ← Limits.pullback.condition, Category.assoc,
      (S1897CoverOver C).w])

/-- **The fibre product square is a scheme pullback square.** -/
theorem S1943PbIsPullback (T : SchemeOverField S1726K) (g : T ⟶ S1726AffineOver) :
    IsPullback (S1943PbFst C T g).left (S1943PbSnd C T g).left
      (S1897CoverOver C).left g.left :=
  IsPullback.of_hasPullback (S1897CoverOver C).left g.left

/-- The fibre product square commutes, as an equation of morphisms over Spec F'. -/
theorem S1943PbSq (T : SchemeOverField S1726K) (g : T ⟶ S1726AffineOver) :
    S1943PbFst C T g ≫ S1897CoverOver C = S1943PbSnd C T g ≫ g := by
  apply Over.OverMorphism.ext
  exact Limits.pullback.condition

/-! ## 2. The 2-commutative square of representable etale stacks -/

/-- The underlying scheme morphism of a vertical composite of Yoneda strong
transformations is the composite of the underlying morphisms. -/
theorem S1943HomOfVcomp {P X Y : SchemeOverField S1726K}
    (L : Pseudofunctor.StrongTrans (S1897Y P) (S1897Y X))
    (M : Pseudofunctor.StrongTrans (S1897Y X) (S1897Y Y)) :
    S1742HomOfStrongTrans (Pseudofunctor.StrongTrans.vcomp L M) =
      S1742HomOfStrongTrans L ≫ S1742HomOfStrongTrans M := by
  have h1 : S1911Val (Pseudofunctor.StrongTrans.vcomp L M)
      (LocallyDiscrete.mk (Opposite.op P)) (Discrete.mk (𝟙 P)) =
      S1911Val L (LocallyDiscrete.mk (Opposite.op P)) (Discrete.mk (𝟙 P)) ≫
        S1742HomOfStrongTrans M := S1911Val_vcomp L M _ _
  have h2 : S1911Val L (LocallyDiscrete.mk (Opposite.op P)) (Discrete.mk (𝟙 P)) =
      𝟙 P ≫ S1742HomOfStrongTrans L :=
    S1742Key L (LocallyDiscrete.mk (Opposite.op P)) (𝟙 P)
  have h3 : S1911Val (Pseudofunctor.StrongTrans.vcomp L M)
      (LocallyDiscrete.mk (Opposite.op P)) (Discrete.mk (𝟙 P)) =
      S1742HomOfStrongTrans (Pseudofunctor.StrongTrans.vcomp L M) := rfl
  rw [← h3, h1, h2, Category.id_comp]

/-- The Yoneda inverses of the two composites agree, because the scheme square
commutes. -/
theorem S1943PbAuxEq (T : SchemeOverField S1726K) (g : T ⟶ S1726AffineOver) :
    S1742HomOfStrongTrans (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (S1943PbFst C T g))
      (S1742StrongTransOfHom (S1897CoverOver C))) =
    S1742HomOfStrongTrans (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (S1943PbSnd C T g))
      (S1742StrongTransOfHom g)) := by
  rw [S1943HomOfVcomp, S1943HomOfVcomp, S1742HomOfStrongTrans_strongTransOfHom,
    S1742HomOfStrongTrans_strongTransOfHom]
  apply Over.OverMorphism.ext
  exact Limits.pullback.condition

/-- **The square of representable stacks is 2-commutative.**  The comparison
2-cell is the 2-Yoneda comparison of the (strict) commutativity of the scheme
pullback square. -/
noncomputable def S1943PbCommutes (T : SchemeOverField S1726K) (g : T ⟶ S1726AffineOver) :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (S1943PbFst C T g))
        (S1742StrongTransOfHom (S1897CoverOver C)))
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (S1943PbSnd C T g))
        (S1742StrongTransOfHom g)) :=
  (S1756IsoOfEvalEq (S1943PbOver C T g) S1726AffineOver
    (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (S1943PbFst C T g))
      (S1742StrongTransOfHom (S1897CoverOver C)))
    (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (S1943PbSnd C T g))
      (S1742StrongTransOfHom g))
    (S1943PbAuxEq C T g)).some

/-- The square of representable etale stacks induced by the scheme fibre
product. -/
noncomputable def S1943StackSquare (T : SchemeOverField S1726K) (g : T ⟶ S1726AffineOver) :
    EtalePseudofunctorSquare (S1897Y (S1943PbOver C T g)) (S1897Y (S1897CoverScheme C))
      (S1897Y T) (S1897Y S1726AffineOver) :=
  EtalePseudofunctorSquare.mk (P := S1897Y (S1943PbOver C T g))
    (X := S1897Y (S1897CoverScheme C)) (Y := S1897Y T) (Z := S1897Y S1726AffineOver)
    (S1742StrongTransOfHom (S1943PbFst C T g)) (S1742StrongTransOfHom (S1943PbSnd C T g))
    (S1742StrongTransOfHom (S1897CoverOver C)) (S1742StrongTransOfHom g)
    (S1943PbCommutes C T g)

/-- **S1911 at the fibre product square**: a two-pullback witness together with
the full 2-universal property. -/
theorem S1943StackWitnessExists (T : SchemeOverField S1726K) (g : T ⟶ S1726AffineOver) :
    ∃ w : (S1943StackSquare C T g).TwoPullbackWitness,
      ∀ (W : EtaleStackPseudofunctor S1726K) (c : (S1943StackSquare C T g).Cone W)
        (phi : Pseudofunctor.StrongTrans W (S1897Y (S1943PbOver C T g))),
        Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi
          (S1943StackSquare C T g).toX) c.toX) →
        Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi
          (S1943StackSquare C T g).toY) c.toY) →
        Nonempty (Iso phi (w.lift W c)) :=
  S1911RepresentableTwoPullbackPullbackSquare_proof (S1897CoverScheme C) T S1726AffineOver
    (S1943PbOver C T g) (S1943PbFst C T g) (S1943PbSnd C T g) (S1897CoverOver C) g
    (S1943PbIsPullback C T g) (S1943StackSquare C T g) rfl rfl rfl rfl

/-- The chosen two-pullback witness. -/
noncomputable def S1943StackWitness (T : SchemeOverField S1726K) (g : T ⟶ S1726AffineOver) :
    (S1943StackSquare C T g).TwoPullbackWitness :=
  Classical.choose (S1943StackWitnessExists C T g)

/-- Its 2-universal property. -/
theorem S1943StackWitness_spec (T : SchemeOverField S1726K) (g : T ⟶ S1726AffineOver) :
    ∀ (W : EtaleStackPseudofunctor S1726K) (c : (S1943StackSquare C T g).Cone W)
      (phi : Pseudofunctor.StrongTrans W (S1897Y (S1943PbOver C T g))),
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi
        (S1943StackSquare C T g).toX) c.toX) →
      Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp phi
        (S1943StackSquare C T g).toY) c.toY) →
      Nonempty (Iso phi ((S1943StackWitness C T g).lift W c)) :=
  Classical.choose_spec (S1943StackWitnessExists C T g)

/-! ## 3. The base-change presentation at a Yoneda point -/

/-- The base-change presentation of the extension map at the Yoneda point
y(g). -/
noncomputable def S1943PresentationOfHom (T : SchemeOverField S1726K)
    (g : T ⟶ S1726AffineOver) :
    EtaleStackBaseChangePresentation (S1897ExtMap C) T (S1742StrongTransOfHom g) where
  pullbackScheme := S1943PbOver C T g
  projection := S1943PbSnd C T g
  projectionMap :=
    { transformation := S1742StrongTransOfHom (S1943PbSnd C T g)
      app_eq := fun U => rfl }
  toSource := S1742StrongTransOfHom (S1943PbFst C T g)
  commutes := S1943PbCommutes C T g
  isPullback := S1943StackWitness C T g

/-- **The full 2-universal property at a Yoneda point.** -/
theorem S1943ConeEssSurjOfHom (T : SchemeOverField S1726K) (g : T ⟶ S1726AffineOver) :
    S1852ConeEssSurj (S1943PresentationOfHom C T g) :=
  S1943StackWitness_spec C T g

/-! ## 4. Moving the last leg of the square along a 2-isomorphism -/

/-- The comparison 2-cell of the presentation with its last leg replaced along e. -/
noncomputable abbrev S1943MovedCommutes (C : S1816Target) (T : SchemeOverField S1726K)
    (g : T ⟶ S1726AffineOver)
    (point : Pseudofunctor.StrongTrans (S1897Y T) (S1897Y S1726AffineOver))
    (e : Iso (S1742StrongTransOfHom g) point) :=
  (S1943PbCommutes C T g).trans
    (S1756WhiskerLeftIso (S1742StrongTransOfHom (S1943PbSnd C T g))
      (S1742StrongTransOfHom g) point e)

/-- The square with its last leg replaced along a 2-isomorphism. -/
noncomputable abbrev S1943MovedSquare (C : S1816Target) (T : SchemeOverField S1726K)
    (g : T ⟶ S1726AffineOver)
    (point : Pseudofunctor.StrongTrans (S1897Y T) (S1897Y S1726AffineOver))
    (e : Iso (S1742StrongTransOfHom g) point) :
    EtalePseudofunctorSquare (S1897Y (S1943PbOver C T g)) (S1897Y (S1897CoverScheme C))
      (S1897Y T) (S1897Y S1726AffineOver) :=
  EtalePseudofunctorSquare.mk (P := S1897Y (S1943PbOver C T g))
    (X := S1897Y (S1897CoverScheme C)) (Y := S1897Y T) (Z := S1897Y S1726AffineOver)
    (S1742StrongTransOfHom (S1943PbFst C T g)) (S1742StrongTransOfHom (S1943PbSnd C T g))
    (S1742StrongTransOfHom (S1897CoverOver C)) point
    (S1943MovedCommutes C T g point e)

/-- A cone over the moved square is a cone over the original square. -/
noncomputable def S1943MovedCone (C : S1816Target) (T : SchemeOverField S1726K)
    (g : T ⟶ S1726AffineOver)
    (point : Pseudofunctor.StrongTrans (S1897Y T) (S1897Y S1726AffineOver))
    (e : Iso (S1742StrongTransOfHom g) point)
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S1943MovedSquare C T g point e).Cone W) : (S1943StackSquare C T g).Cone W where
  toX := c.toX
  toY := c.toY
  commutes := c.commutes.trans
    (S1756WhiskerLeftIso c.toY (S1742StrongTransOfHom g) point e).symm

/-- A cone morphism over the moved square is a cone morphism over the original
square.  Its compatibility equation lives in 2-cells into a representable stack,
hence is a subsingleton. -/
noncomputable def S1943MovedConeMorphism (C : S1816Target) (T : SchemeOverField S1726K)
    (g : T ⟶ S1726AffineOver)
    (point : Pseudofunctor.StrongTrans (S1897Y T) (S1897Y S1726AffineOver))
    (e : Iso (S1742StrongTransOfHom g) point)
    {W : EtaleStackPseudofunctor S1726K}
    {s t : (S1943MovedSquare C T g point e).Cone W}
    (m : (S1943MovedSquare C T g point e).ConeMorphism s t) :
    (S1943StackSquare C T g).ConeMorphism (S1943MovedCone C T g point e s)
      (S1943MovedCone C T g point e t) where
  toX := m.toX
  toY := m.toY
  compatibility := by
    haveI : Subsingleton
        (Pseudofunctor.StrongTrans.vcomp (S1943MovedCone C T g point e s).toX
            (S1943StackSquare C T g).xToBase ⟶
          Pseudofunctor.StrongTrans.vcomp (S1943MovedCone C T g point e t).toY
            (S1943StackSquare C T g).yToBase) :=
      S1897Modification_subsingleton_representable _ _
    exact Subsingleton.elim _ _

/-- The two-pullback witness of the moved square: every field is the original
field evaluated at the adjusted cone. -/
noncomputable def S1943MovedWitness (C : S1816Target) (T : SchemeOverField S1726K)
    (g : T ⟶ S1726AffineOver)
    (point : Pseudofunctor.StrongTrans (S1897Y T) (S1897Y S1726AffineOver))
    (e : Iso (S1742StrongTransOfHom g) point) :
    (S1943MovedSquare C T g point e).TwoPullbackWitness where
  lift W c := (S1943StackWitness C T g).lift W (S1943MovedCone C T g point e c)
  liftToX W c := (S1943StackWitness C T g).liftToX W (S1943MovedCone C T g point e c)
  liftToY W c := (S1943StackWitness C T g).liftToY W (S1943MovedCone C T g point e c)
  liftTwoCell W s t m :=
    (S1943StackWitness C T g).liftTwoCell W (S1943MovedCone C T g point e s)
      (S1943MovedCone C T g point e t) (S1943MovedConeMorphism C T g point e m)
  liftTwoCell_toX W s t m :=
    (S1943StackWitness C T g).liftTwoCell_toX W (S1943MovedCone C T g point e s)
      (S1943MovedCone C T g point e t) (S1943MovedConeMorphism C T g point e m)
  liftTwoCell_toY W s t m :=
    (S1943StackWitness C T g).liftTwoCell_toY W (S1943MovedCone C T g point e s)
      (S1943MovedCone C T g point e t) (S1943MovedConeMorphism C T g point e m)
  twoCell_ext W first second alpha beta h1 h2 :=
    (S1943StackWitness C T g).twoCell_ext W alpha beta h1 h2

/-- The base-change presentation of the extension map at the moved point. -/
noncomputable def S1943MovedPresentation (C : S1816Target) (T : SchemeOverField S1726K)
    (g : T ⟶ S1726AffineOver)
    (point : Pseudofunctor.StrongTrans (S1897Y T) (S1897Y S1726AffineOver))
    (e : Iso (S1742StrongTransOfHom g) point) :
    EtaleStackBaseChangePresentation (S1897ExtMap C) T point where
  pullbackScheme := S1943PbOver C T g
  projection := S1943PbSnd C T g
  projectionMap :=
    { transformation := S1742StrongTransOfHom (S1943PbSnd C T g)
      app_eq := fun U => rfl }
  toSource := S1742StrongTransOfHom (S1943PbFst C T g)
  commutes := S1943MovedCommutes C T g point e
  isPullback := S1943MovedWitness C T g point e

/-- **The full 2-universal property transports along a 2-isomorphism of the
point.** -/
theorem S1943MovedConeEssSurj (C : S1816Target) (T : SchemeOverField S1726K)
    (g : T ⟶ S1726AffineOver)
    (point : Pseudofunctor.StrongTrans (S1897Y T) (S1897Y S1726AffineOver))
    (e : Iso (S1742StrongTransOfHom g) point)
    (h : S1852ConeEssSurj (S1943PresentationOfHom C T g)) :
    S1852ConeEssSurj (S1943MovedPresentation C T g point e) := by
  intro W c phi h1 h2
  exact h W (S1943MovedCone C T g point e c) phi h1 h2

/-! ## 5. The strong finite-etale structure on the extension map -/

/-- The strong base-change presentation at an arbitrary scheme-valued point of
the orbicurve stack, obtained by 2-Yoneda from the point and S1911. -/
noncomputable def S1943BaseChange (C : S1816Target) (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1897Y T) (S1897Y S1726AffineOver)) :
    StrongEtaleStackBaseChangePresentation (S1897ExtMap C) T point where
  toWeak := S1943MovedPresentation C T (S1742HomOfStrongTrans point) point
    (S1742StrongTransIsoOfHom point)
  coneEssSurj := S1943MovedConeEssSurj C T (S1742HomOfStrongTrans point) point
    (S1742StrongTransIsoOfHom point)
    (S1943ConeEssSurjOfHom C T (S1742HomOfStrongTrans point))

/-- **The projection of the presentation at a point is finite and etale**: it is
the base change of the finite etale structure morphism of C. -/
theorem S1943HasProperty (C : S1816Target) (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1897Y T) (S1897Y S1726AffineOver)) :
    IsFinite ((S1943BaseChange C T point).toWeak.projection.left) ∧
      Etale ((S1943BaseChange C T point).toWeak.projection.left) := by
  have h := FiniteEtaleCover.finiteEtale_pullback (f := (S1897CoverOver C).left)
    (g := (S1742HomOfStrongTrans point).left) C.property.1 C.property.2
  exact ⟨h.2, h.1⟩

/-- **Every finite etale cover of Spec R' has a strong finite-etale extension
map.**  This is S1897's extension datum, without its literal identity
requirement. -/
noncomputable def S1943Strong (C : S1816Target) :
    StrongEtaleStackFiniteEtaleMorphism (S1897ExtMap C) where
  baseChange T point := S1943BaseChange C T point
  hasProperty T point := S1943HasProperty C T point

/-! ## 6. The identity-point model is the cover itself -/

/-- The identity point in 2-Yoneda form is the identity morphism. -/
theorem S1943HomOfBasePoint :
    S1742HomOfStrongTrans (F := S1726K) (S := S1726AffineOver) (T := S1726AffineOver)
      S1733BasePoint = 𝟙 S1726AffineOver := by
  show (((Pseudofunctor.StrongTrans.id (S1897Y S1726AffineOver)).app
    (LocallyDiscrete.mk (Opposite.op S1726AffineOver))).toFunctor.obj
      (Discrete.mk (𝟙 S1726AffineOver))).as = 𝟙 S1726AffineOver
  rw [show (Pseudofunctor.StrongTrans.id (S1897Y S1726AffineOver)).app
      (LocallyDiscrete.mk (Opposite.op S1726AffineOver)) =
      𝟙 ((S1897Y S1726AffineOver).obj
        (LocallyDiscrete.mk (Opposite.op S1726AffineOver))) from rfl]
  rw [Cat.Hom.id_toFunctor]
  rfl

/-- The underlying scheme morphism of the identity point. -/
noncomputable abbrev S1943BasePointHom : (S1726AffineOver).left ⟶ (S1726AffineOver).left :=
  (S1742HomOfStrongTrans (F := S1726K) (S := S1726AffineOver) (T := S1726AffineOver)
    S1733BasePoint).left

/-- The underlying scheme morphism of the identity point is the identity. -/
theorem S1943BasePointHom_eq : S1943BasePointHom = 𝟙 (S1726AffineOver).left := by
  rw [S1943BasePointHom]
  rw [S1943HomOfBasePoint]
  rfl

/-- **Base change along a morphism equal to the identity is the identity**: the
first projection of the fibre product of `f` with `g = 𝟙` is an isomorphism. -/
noncomputable def S1943PullbackAlongIdIso {X S : Scheme} (f : X ⟶ S) {g : S ⟶ S}
    (hg : g = 𝟙 S) : Limits.pullback f g ≅ X where
  hom := Limits.pullback.fst f g
  inv := Limits.pullback.lift (𝟙 X) f (by rw [hg]; simp)
  hom_inv_id := by
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, Limits.pullback.lift_fst, Category.comp_id,
        Category.id_comp]
    · simp only [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.condition, hg,
        Category.comp_id, Category.id_comp]
  inv_hom_id := by
    simp only [Limits.pullback.lift_fst]

/-- **The identity-point model of the extension cover is the cover itself, over
`Spec R'`.**  The projection is the second leg of the fibre product of
`C -> Spec R'` with the identity. -/
noncomputable def S1943ModelIso (C : S1816Target) :
    (Over.mk (Limits.pullback.snd (f := (S1897CoverOver C).left) (g := S1943BasePointHom))) ≅
      C.obj :=
  Over.isoMk (S1943PullbackAlongIdIso (S1897CoverOver C).left S1943BasePointHom_eq) (by
    show Limits.pullback.fst (S1897CoverOver C).left S1943BasePointHom ≫
        (S1897CoverOver C).left =
      Limits.pullback.snd (f := (S1897CoverOver C).left) (g := S1943BasePointHom)
    rw [Limits.pullback.condition, S1943BasePointHom_eq]
    simp only [Category.comp_id])

/-- **The affine model of the coherent extension cover is `C` up to
isomorphism.**  This replaces S1897's literal identity `idPresentation` by the
canonical isomorphism `pullback f 1 ≅ X`. -/
theorem S1943S1816Obj_iso (C : S1816Target) :
    Nonempty (S1816Obj (S1897ExtCover C (S1943Strong C)) ≅ C) := by
  refine ⟨ObjectProperty.isoMk
    (P := fun X : Over S1816Base => IsFiniteEtaleHom X.hom) ?_⟩
  show (Over.mk (Limits.pullback.snd (f := (S1897CoverOver C).left)
    (g := S1943BasePointHom))) ≅ C.obj
  exact S1943ModelIso C

/-! ## 7. Essential surjectivity -/

/-- **`S1878EssSurj`, unconditionally.**  Every finite etale cover of `Spec R'`
is isomorphic, over `Spec R'`, to the affine model of a coherent cover. -/
theorem S1943EssSurj : S1878EssSurj := by
  intro C
  exact ⟨S1897ExtCoherent C (S1943Strong C), S1943S1816Obj_iso C⟩

/-- The canonical comparison functor is an equivalence. -/
theorem S1943Functor_isEquivalence : S1878Functor.IsEquivalence :=
  S1878Functor_isEquivalence_iff_essSurj.mpr S1943EssSurj

/-- The composite comparison with the affine slice is an equivalence. -/
theorem S1943FunctorToSlice_isEquivalence : S1878FunctorToSlice.IsEquivalence :=
  S1878FunctorToSlice_isEquivalence_iff_essSurj.mpr S1943EssSurj

/-- The object-level form: every finite etale cover of `Spec R'` is the affine
model of a coherent cover. -/
theorem S1943ModelEssSurj : S1897ModelEssSurj := by
  intro C
  obtain ⟨A, ⟨e⟩⟩ := S1943EssSurj C
  exact ⟨A, ⟨(FiniteEtaleCover.forgetOver S1816Base).mapIso e⟩⟩

/-! ## 8. Checks and axiom footprint -/

#check S1943PbOver
#check S1943PbIsPullback
#check S1943HomOfVcomp
#check S1943PbCommutes
#check S1943StackSquare
#check S1943StackWitness
#check S1943PresentationOfHom
#check S1943ConeEssSurjOfHom
#check S1943MovedPresentation
#check S1943MovedConeEssSurj
#check S1943BaseChange
#check S1943HasProperty
#check S1943Strong
#check S1943HomOfBasePoint
#check S1943BasePointHom_eq
#check S1943PullbackAlongIdIso
#check S1943ModelIso
#check S1943S1816Obj_iso
#check S1943EssSurj
#check S1943Functor_isEquivalence
#check S1943FunctorToSlice_isEquivalence
#check S1943ModelEssSurj

#print axioms S1943PbIsPullback
#print axioms S1943HomOfVcomp
#print axioms S1943PbCommutes
#print axioms S1943StackWitness
#print axioms S1943ConeEssSurjOfHom
#print axioms S1943MovedWitness
#print axioms S1943MovedConeEssSurj
#print axioms S1943BaseChange
#print axioms S1943HasProperty
#print axioms S1943Strong
#print axioms S1943HomOfBasePoint
#print axioms S1943PullbackAlongIdIso
#print axioms S1943ModelIso
#print axioms S1943S1816Obj_iso
#print axioms S1943EssSurj
#print axioms S1943Functor_isEquivalence
#print axioms S1943ModelEssSurj

end LeanFormal.IUT.XiFPaper.S1943AssembleEssSurjActual
