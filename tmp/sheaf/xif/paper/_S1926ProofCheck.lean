import tmp.sheaf.xif.paper.S1913S1726CompactificationActual
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# S1926: the representable open immersion of the actual compactification map

S1913 reduced the remaining 2-categorical input of the actual D9 cusp to the
representable open immersion of the stack map

    S1742StrongTransOfHom (C.openMap) : S1726Orbicurve.stack -> stack(P)

induced by the open immersion `Spec R' -> P` of a compactification datum
`C : S1913AffineCompactification`.  S1913 named exactly this statement
`S1913RepresentableOpenImmersion C` and left it open.

This file constructs it, for every compactification datum `C`, from the actual
scheme fibre product.  For every test scheme `T` and every scheme-valued point
`point : h_T -> h_P` of the compactification stack, the 2-Yoneda comparison of
S1742 turns `point` into an actual morphism `t : T -> P` of schemes over `F'`.
The base change of the open immersion along `t` is therefore the actual
schematic fibre product

    P_T := T x_P Spec R' ,

with its two projections `pX : P_T -> Spec R'` and `pT : P_T -> T`.  The
2-commutative square is the square of representable etale stacks induced by this
scheme pullback square, and the full `TwoPullbackWitness` is constructed
pointwise from `IsPullback.lift`:

* the lift of a cone is, at every test object and every object of its source
  fibre, the pullback lift of the two scheme morphisms given by the cone;
* the comparison 2-cells are the two projection formulae `lift_fst` and
  `lift_snd`;
* the action on cone morphisms is pullback uniqueness;
* the two 2-cell coherence fields and 2-cell extensionality are the genuine
  discreteness of the represented target: a represented etale stack has
  subsingleton 2-cells (S1896's `S1896Modification_subsingleton`).

No hypothetical 2-cell is introduced.  The projection `pT` is an open
immersion because it is the base change of the open immersion `C.openMap`
(Mathlib's `IsOpenImmersion (pullback.snd f g)` instance).  Consequently
`S1913RepresentableOpenImmersion C` is proved for every `C`, and the actual
cusp follows from the scheme-level compactification datum `C` alone.

The scheme-level projective compactification itself is *not* constructed here:
that is the separate S1913 first missing datum `S1913AffineCompactification`.
This file closes exactly the 2-categorical input (b), not (a).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1926RepresentableOpenImmersionActual

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1896BoundaryCuspActual
open LeanFormal.IUT.XiFPaper.S1913S1726CompactificationActual

/-! ## 1. The actual scheme fibre product -/

/-- The underlying scheme morphism of a scheme-valued point of the
compactification stack, via the 2-Yoneda comparison of S1742. -/
noncomputable def S1926PointHom (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme)) : T ⟶ C.scheme :=
  S1742HomOfStrongTrans (F := S1726K) point

/-- The actual scheme fibre product `T x_P Spec R'`. -/
noncomputable abbrev S1926PullbackScheme (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme)) : SchemeOverField S1726K :=
  Over.mk (pullback.fst C.openMap.left (S1926PointHom C T point).left ≫ S1726AffineOver.hom)

/-- The projection to the affine model. -/
noncomputable def S1926ToSource (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme)) :
    S1926PullbackScheme C T point ⟶ S1726AffineOver :=
  Over.homMk (pullback.fst C.openMap.left (S1926PointHom C T point).left) (by rfl)

/-- The projection to the test scheme. -/
noncomputable def S1926Projection (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme)) :
    S1926PullbackScheme C T point ⟶ T :=
  Over.homMk (pullback.snd C.openMap.left (S1926PointHom C T point).left) (by
    show pullback.snd C.openMap.left (S1926PointHom C T point).left ≫ T.hom =
      pullback.fst C.openMap.left (S1926PointHom C T point).left ≫ S1726AffineOver.hom
    rw [← (S1926PointHom C T point).w, ← C.openMap.w]
    rw [← Category.assoc, ← Category.assoc]
    rw [← pullback.condition])

/-- The scheme pullback square underlying the stack square. -/
theorem S1926IsPullback (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme)) :
    IsPullback (S1926ToSource C T point).left (S1926Projection C T point).left
      C.openMap.left (S1926PointHom C T point).left :=
  IsPullback.of_hasPullback C.openMap.left (S1926PointHom C T point).left

/-! ## 2. Values of strong transformations into representable stacks -/

/-- The value of a strong transformation into a representable etale stack. -/
noncomputable def S1926Val {W : EtaleStackPseudofunctor S1726K} {S : SchemeOverField S1726K}
    (L : Pseudofunctor.StrongTrans W (S1742YS (F := S1726K) S))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) : U.as.unop ⟶ S :=
  ((L.app U).toFunctor.obj a).as

/-- The value of the 2-Yoneda transformation. -/
theorem S1926Val_strongTransOfHom {S T : SchemeOverField S1726K} (f : S ⟶ T)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (a : (S1742YS (F := S1726K) S).obj U) :
    S1926Val (S1742StrongTransOfHom (F := S1726K) f) U a = a.as ≫ f := by
  change ((S1742App (F := S1726K) f U).toFunctor.obj a).as = a.as ≫ f
  rw [← Discrete.mk_as a, S1742App_obj]

/-- The component of a vertical composite is the composite of the components. -/
theorem S1926App_vcomp {W : EtaleStackPseudofunctor S1726K} {S T : SchemeOverField S1726K}
    (L : Pseudofunctor.StrongTrans W (S1742YS (F := S1726K) S))
    (M : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) S) (S1742YS (F := S1726K) T))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp L M).app U = L.app U ≫ M.app U := rfl

/-- Composition with a strong transformation of representable stacks acts on values
by composition of scheme morphisms. -/
theorem S1926Val_vcomp {W : EtaleStackPseudofunctor S1726K} {S T : SchemeOverField S1726K}
    (L : Pseudofunctor.StrongTrans W (S1742YS (F := S1726K) S))
    (M : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) S) (S1742YS (F := S1726K) T))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    S1926Val (Pseudofunctor.StrongTrans.vcomp L M) U a =
      S1926Val L U a ≫ S1742HomOfStrongTrans (F := S1726K) M := by
  rw [S1926Val, S1926Val, S1926App_vcomp, S1742Comp_toFunctor_obj,
    ← S1742AppEq (F := S1726K) M U, ← Discrete.mk_as ((L.app U).toFunctor.obj a),
    S1742App_obj (F := S1726K) (S1742HomOfStrongTrans (F := S1726K) M) U]

/-- The value of a strong transformation into a representable stack is natural. -/
theorem S1926Val_naturality {W : EtaleStackPseudofunctor S1726K} {S : SchemeOverField S1726K}
    (L : Pseudofunctor.StrongTrans W (S1742YS (F := S1726K) S))
    {a b : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : a ⟶ b) (x : W.obj a) :
    S1926Val L b ((W.map φ).toFunctor.obj x) = φ.as.unop ≫ S1926Val L a x := by
  rw [S1926Val, S1926Val]
  have h := Discrete.eq_of_hom ((L.naturality φ).hom.toNatTrans.app x)
  rw [S1742Comp_toFunctor_obj, S1742Comp_toFunctor_obj, S1742YS_map (F := S1726K) S φ,
    ← Discrete.mk_as ((L.app a).toFunctor.obj x), S1742Fiber_map_obj] at h
  exact h

/-- A 2-isomorphism between strong transformations of represented stacks from
pointwise equality of their underlying scheme morphisms. -/
noncomputable def S1926IsoOfValEq {S T : SchemeOverField S1726K}
    (eta theta : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) S)
      (S1742YS (F := S1726K) T))
    (h : ∀ (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
      (a : (S1742YS (F := S1726K) S).obj U), S1926Val eta U a = S1926Val theta U a) :
    Iso eta theta :=
  Pseudofunctor.StrongTrans.isoMk
    (fun U => Cat.Hom.isoMk (eqToIso (CategoryTheory.Functor.ext
      (fun a => Discrete.ext (h U a))
      (by
        intro X Y f
        apply ULift.ext
        exact Subsingleton.elim _ _))))
    (by
      intro a b g
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext X
      apply ULift.ext
      exact Subsingleton.elim _ _)

/-! ## 3. The 2-commutative square of representable stacks -/

/-- The square commutes on underlying scheme morphisms. -/
theorem S1926SquareCommutesHom (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme)) :
    S1926ToSource C T point ≫ C.openMap =
      S1926Projection C T point ≫ S1926PointHom C T point := by
  apply Over.OverMorphism.ext
  show pullback.fst C.openMap.left (S1926PointHom C T point).left ≫ C.openMap.left =
    pullback.snd C.openMap.left (S1926PointHom C T point).left ≫
      (S1926PointHom C T point).left
  exact pullback.condition

/-- Pointwise commutation of the square of represented stacks. -/
theorem S1926CommutesVal (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (a : (S1742YS (F := S1726K) (S1926PullbackScheme C T point)).obj U) :
    S1926Val (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) (S1926ToSource C T point))
        (S1742StrongTransOfHom (F := S1726K) C.openMap)) U a =
      S1926Val (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) (S1926Projection C T point))
        point) U a := by
  rw [S1926Val_vcomp, S1926Val_vcomp]
  rw [S1926Val_strongTransOfHom, S1926Val_strongTransOfHom]
  rw [S1742HomOfStrongTrans_strongTransOfHom]
  calc
    (a.as ≫ S1926ToSource C T point) ≫ C.openMap
        = a.as ≫ (S1926ToSource C T point ≫ C.openMap) := by rw [Category.assoc]
    _ = a.as ≫ (S1926Projection C T point ≫ S1926PointHom C T point) := by
          rw [S1926SquareCommutesHom]
    _ = (a.as ≫ S1926Projection C T point) ≫ S1926PointHom C T point := by
          rw [Category.assoc]

/-- The square of represented etale stacks induced by the scheme fibre product. -/
noncomputable def S1926Square (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme)) :
    EtalePseudofunctorSquare (S1742YS (F := S1726K) (S1926PullbackScheme C T point))
      (S1742YS (F := S1726K) S1726AffineOver)
      (S1742YS (F := S1726K) T) (S1742YS (F := S1726K) C.scheme) where
  toX := S1742StrongTransOfHom (F := S1726K) (S1926ToSource C T point)
  toY := S1742StrongTransOfHom (F := S1726K) (S1926Projection C T point)
  xToBase := S1742StrongTransOfHom (F := S1726K) C.openMap
  yToBase := point
  commutes := S1926IsoOfValEq _ _ (S1926CommutesVal C T point)

/-! ## 4. The pointwise lift of a cone, by scheme pullback -/

/-- The cone condition on underlying scheme morphisms. -/
theorem S1926ConeCondition (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme))
    {W : EtaleStackPseudofunctor S1726K} (c : (S1926Square C T point).Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (a : W.obj U) :
    S1926Val c.toX U a ≫ C.openMap = S1926Val c.toY U a ≫ S1926PointHom C T point := by
  have h := Discrete.eq_of_hom ((c.commutes.hom.as.app U).toNatTrans.app a)
  change S1926Val (Pseudofunctor.StrongTrans.vcomp c.toX (S1926Square C T point).xToBase) U a =
    S1926Val (Pseudofunctor.StrongTrans.vcomp c.toY (S1926Square C T point).yToBase) U a at h
  rw [S1926Val_vcomp, S1926Val_vcomp] at h
  rw [show (S1926Square C T point).xToBase =
      S1742StrongTransOfHom (F := S1726K) C.openMap from rfl,
    show (S1926Square C T point).yToBase = point from rfl] at h
  rw [S1742HomOfStrongTrans_strongTransOfHom] at h
  exact h

/-- The pointwise lift of a cone in the scheme fibre product. -/
noncomputable def S1926LiftSchemeVal (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme))
    {W : EtaleStackPseudofunctor S1726K} (c : (S1926Square C T point).Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    U.as.unop.left ⟶ (S1926PullbackScheme C T point).left :=
  (S1926IsPullback C T point).lift (S1926Val c.toX U a).left (S1926Val c.toY U a).left
    (congrArg Over.Hom.left (S1926ConeCondition C T point c U a))

/-- The pointwise lift as a morphism over the base field. -/
noncomputable def S1926LiftVal (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme))
    {W : EtaleStackPseudofunctor S1726K} (c : (S1926Square C T point).Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    U.as.unop ⟶ S1926PullbackScheme C T point :=
  Over.homMk (S1926LiftSchemeVal C T point c U a) (by
    change (S1926LiftSchemeVal C T point c U a ≫
        (S1926ToSource C T point).left) ≫ S1726AffineOver.hom = U.as.unop.hom
    simp only [S1926LiftSchemeVal, IsPullback.lift_fst]
    exact Over.w (S1926Val c.toX U a))

/-- The lift projects to the affine model. -/
theorem S1926LiftVal_fst (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme))
    {W : EtaleStackPseudofunctor S1726K} (c : (S1926Square C T point).Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    S1926LiftVal C T point c U a ≫ S1926ToSource C T point =
      S1926Val c.toX U a := by
  apply Over.OverMorphism.ext
  change (S1926LiftVal C T point c U a).left ≫ (S1926ToSource C T point).left =
    (S1926Val c.toX U a).left
  change (S1926LiftSchemeVal C T point c U a ≫
      (S1926ToSource C T point).left) = (S1926Val c.toX U a).left
  simp only [S1926LiftSchemeVal, IsPullback.lift_fst]

/-- The lift projects to the test scheme. -/
theorem S1926LiftVal_snd (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme))
    {W : EtaleStackPseudofunctor S1726K} (c : (S1926Square C T point).Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (a : W.obj U) :
    S1926LiftVal C T point c U a ≫ S1926Projection C T point =
      S1926Val c.toY U a := by
  apply Over.OverMorphism.ext
  change (S1926LiftVal C T point c U a).left ≫ (S1926Projection C T point).left =
    (S1926Val c.toY U a).left
  change (S1926LiftSchemeVal C T point c U a ≫
      (S1926Projection C T point).left) = (S1926Val c.toY U a).left
  simp only [S1926LiftSchemeVal, IsPullback.lift_snd]

/-- The lift is constant on the objects of the source fibre. -/
theorem S1926LiftVal_eq_of_hom (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme))
    {W : EtaleStackPseudofunctor S1726K} (c : (S1926Square C T point).Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    {a b : W.obj U} (m : a ⟶ b) :
    S1926LiftVal C T point c U a = S1926LiftVal C T point c U b := by
  apply Over.OverMorphism.ext
  apply IsPullback.hom_ext (S1926IsPullback C T point)
  · have h1 : (S1926LiftVal C T point c U a).left ≫
        (S1926ToSource C T point).left = (S1926Val c.toX U a).left :=
      congrArg Over.Hom.left (S1926LiftVal_fst C T point c U a)
    have h2 : (S1926LiftVal C T point c U b).left ≫
        (S1926ToSource C T point).left = (S1926Val c.toX U b).left :=
      congrArg Over.Hom.left (S1926LiftVal_fst C T point c U b)
    calc
      (S1926LiftVal C T point c U a).left ≫ (S1926ToSource C T point).left
          = (S1926Val c.toX U a).left := h1
      _ = (S1926Val c.toX U b).left :=
            congrArg Over.Hom.left
              (Discrete.eq_of_hom ((c.toX.app U).toFunctor.map m))
      _ = (S1926LiftVal C T point c U b).left ≫
            (S1926ToSource C T point).left := h2.symm
  · have h1 : (S1926LiftVal C T point c U a).left ≫
        (S1926Projection C T point).left = (S1926Val c.toY U a).left :=
      congrArg Over.Hom.left (S1926LiftVal_snd C T point c U a)
    have h2 : (S1926LiftVal C T point c U b).left ≫
        (S1926Projection C T point).left = (S1926Val c.toY U b).left :=
      congrArg Over.Hom.left (S1926LiftVal_snd C T point c U b)
    calc
      (S1926LiftVal C T point c U a).left ≫ (S1926Projection C T point).left
          = (S1926Val c.toY U a).left := h1
      _ = (S1926Val c.toY U b).left :=
            congrArg Over.Hom.left
              (Discrete.eq_of_hom ((c.toY.app U).toFunctor.map m))
      _ = (S1926LiftVal C T point c U b).left ≫
            (S1926Projection C T point).left := h2.symm

/-- The lift is natural in the test object. -/
theorem S1926LiftVal_natural (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme))
    {W : EtaleStackPseudofunctor S1726K} (c : (S1926Square C T point).Cone W)
    {a b : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (g : a ⟶ b)
    (x : W.obj a) :
    S1926LiftVal C T point c b ((W.map g).toFunctor.obj x) =
      g.as.unop ≫ S1926LiftVal C T point c a x := by
  apply Over.OverMorphism.ext
  apply IsPullback.hom_ext (S1926IsPullback C T point)
  · change (S1926LiftVal C T point c b ((W.map g).toFunctor.obj x)).left ≫
        (S1926ToSource C T point).left =
      (g.as.unop ≫ S1926LiftVal C T point c a x).left ≫
        (S1926ToSource C T point).left
    have h1 : (S1926LiftVal C T point c b ((W.map g).toFunctor.obj x)).left ≫
        (S1926ToSource C T point).left =
        (S1926Val c.toX b ((W.map g).toFunctor.obj x)).left :=
      congrArg Over.Hom.left
        (S1926LiftVal_fst C T point c b ((W.map g).toFunctor.obj x))
    have h2 : (S1926LiftVal C T point c a x).left ≫
        (S1926ToSource C T point).left = (S1926Val c.toX a x).left :=
      congrArg Over.Hom.left (S1926LiftVal_fst C T point c a x)
    calc
      (S1926LiftVal C T point c b ((W.map g).toFunctor.obj x)).left ≫
          (S1926ToSource C T point).left
          = (S1926Val c.toX b ((W.map g).toFunctor.obj x)).left := h1
      _ = (g.as.unop ≫ S1926Val c.toX a x).left :=
            congrArg Over.Hom.left (S1926Val_naturality c.toX g x)
      _ = (g.as.unop).left ≫ (S1926Val c.toX a x).left := rfl
      _ = (g.as.unop).left ≫ ((S1926LiftVal C T point c a x).left ≫
            (S1926ToSource C T point).left) := by rw [h2]
      _ = (g.as.unop ≫ S1926LiftVal C T point c a x).left ≫
            (S1926ToSource C T point).left := rfl
  · change (S1926LiftVal C T point c b ((W.map g).toFunctor.obj x)).left ≫
        (S1926Projection C T point).left =
      (g.as.unop ≫ S1926LiftVal C T point c a x).left ≫
        (S1926Projection C T point).left
    have h1 : (S1926LiftVal C T point c b ((W.map g).toFunctor.obj x)).left ≫
        (S1926Projection C T point).left =
        (S1926Val c.toY b ((W.map g).toFunctor.obj x)).left :=
      congrArg Over.Hom.left
        (S1926LiftVal_snd C T point c b ((W.map g).toFunctor.obj x))
    have h2 : (S1926LiftVal C T point c a x).left ≫
        (S1926Projection C T point).left = (S1926Val c.toY a x).left :=
      congrArg Over.Hom.left (S1926LiftVal_snd C T point c a x)
    calc
      (S1926LiftVal C T point c b ((W.map g).toFunctor.obj x)).left ≫
          (S1926Projection C T point).left
          = (S1926Val c.toY b ((W.map g).toFunctor.obj x)).left := h1
      _ = (g.as.unop ≫ S1926Val c.toY a x).left :=
            congrArg Over.Hom.left (S1926Val_naturality c.toY g x)
      _ = (g.as.unop).left ≫ (S1926Val c.toY a x).left := rfl
      _ = (g.as.unop).left ≫ ((S1926LiftVal C T point c a x).left ≫
            (S1926Projection C T point).left) := by rw [h2]
      _ = (g.as.unop ≫ S1926LiftVal C T point c a x).left ≫
            (S1926Projection C T point).left := rfl


example (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme))
    {W : EtaleStackPseudofunctor S1726K} (c : (S1926Square C T point).Cone W)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (a b : W.obj U) (m : a ⟶ b) :
    (Discrete.mk (S1926LiftVal C T point c U a) : Discrete (U.as.unop ⟶ S1926PullbackScheme C T point)) ⟶
      Discrete.mk (S1926LiftVal C T point c U b) :=
  ULift.up (PLift.up (S1926LiftVal_eq_of_hom C T point c U m))

end LeanFormal.IUT.XiFPaper.S1926RepresentableOpenImmersionActual
