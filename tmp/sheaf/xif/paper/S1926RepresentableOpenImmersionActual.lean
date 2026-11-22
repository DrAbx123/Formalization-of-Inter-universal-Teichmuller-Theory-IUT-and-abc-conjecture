import tmp.sheaf.xif.paper.S1913S1726CompactificationActual
import tmp.sheaf.xif.paper.S1911RepresentableTwoPullbackActual
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# S1926: the representable open immersion of the actual compactification map

S1913 reduced the remaining 2-categorical input of the actual D9 cusp to the
representable open immersion of the stack map

    S1742StrongTransOfHom C.openMap : S1726Orbicurve.stack -> stack(P)

induced by the open immersion `Spec R' -> P` of a compactification datum
`C : S1913AffineCompactification`.  S1913 named exactly this statement
`S1913RepresentableOpenImmersion C` and left it open.

This file constructs it for every compactification datum `C` from the actual
scheme fibre product.  For every test scheme `T` and every scheme-valued point
`point : h_T -> h_P` of the compactification stack, the 2-Yoneda comparison of
S1742 turns `point` into an actual morphism `t : T -> P` of schemes over
`F'`.  The base change of the open immersion along `t` is the actual
schematic fibre product

    P_T := T x_P Spec R' ,

with its two projections `pX : P_T -> Spec R'` and `pT : P_T -> T`.  The
2-commutative square is the square of representable etale stacks induced by this
scheme pullback square.

The full `TwoPullbackWitness` is supplied by S1911's corrected two-pullback
theorem (`S1911Witness`): for a genuine pullback square of schemes over `F'`,
the square of represented etale stacks is a bicategorical pullback, with the
lift built pointwise from `IsPullback.lift` and all comparison 2-cells from
the discreteness of a represented target.  Nothing here is a hypothetical
2-cell: S1911's witness is a theorem and this file only instantiates it at the
scheme fibre product of S1913's open immersion.

Finally `pT` is an open immersion because it is the base change of the open
immersion `C.openMap` (Mathlib's `IsOpenImmersion (pullback.snd f g)`
instance).  Hence `S1913RepresentableOpenImmersion C` is proved for every
`C`, and the actual cusp follows from the scheme-level compactification datum
`C` alone.

The scheme-level projective compactification itself is *not* constructed here:
that is the separate S1913 first missing datum `S1913AffineCompactification`.
This file closes the 2-categorical input (b), not (a).
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
open LeanFormal.IUT.XiFPaper.S1911RepresentableTwoPullbackActual
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

/-! ## 4. The full 2-pullback witness, instantiated from S1911 -/

/-- **The square is a bicategorical pullback.**  S1911's corrected two-pullback
theorem applies to the scheme fibre-product square of `C.openMap` along the
2-Yoneda morphism of the point. -/
noncomputable def S1926TwoPullbackWitness (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme)) :
    (S1926Square C T point).TwoPullbackWitness := by
  let sq := S1926Square C T point
  have hF : S1911BaseF sq = C.openMap := by
    change S1742HomOfStrongTrans (F := S1726K) sq.xToBase = C.openMap
    rw [show sq.xToBase = S1742StrongTransOfHom (F := S1726K) C.openMap from rfl,
      S1742HomOfStrongTrans_strongTransOfHom]
  have hG : S1911BaseG sq = S1926PointHom C T point := rfl
  have hpb : IsPullback (S1926ToSource C T point).left (S1926Projection C T point).left
      (S1911BaseF sq).left (S1911BaseG sq).left := by
    rw [hF, hG]
    exact S1926IsPullback C T point
  exact S1911Witness (P := S1926PullbackScheme C T point)
    (pX := S1926ToSource C T point) (pY := S1926Projection C T point)
    (sq := sq) hpb rfl rfl

/-! ## 5. The base-change presentation and the representable open immersion -/

/-- The actual base-change presentation of the compactification map at a point. -/
noncomputable def S1926BaseChange (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme)) :
    EtaleStackBaseChangePresentation C.S1913StackOpenMap T point where
  pullbackScheme := S1926PullbackScheme C T point
  projection := S1926Projection C T point
  projectionMap :=
    { transformation := S1742StrongTransOfHom (F := S1726K) (S1926Projection C T point)
      app_eq := fun U => rfl }
  toSource := S1742StrongTransOfHom (F := S1726K) (S1926ToSource C T point)
  commutes := (S1926Square C T point).commutes
  isPullback := S1926TwoPullbackWitness C T point

/-- The projection is an open immersion: it is the base change of the open
immersion of the affine model. -/
theorem S1926Projection_isOpenImmersion (C : S1913AffineCompactification)
    (T : SchemeOverField S1726K)
    (point : Pseudofunctor.StrongTrans (S1742YS (F := S1726K) T)
      (S1742YS (F := S1726K) C.scheme)) :
    IsOpenImmersion (S1926Projection C T point).left := by
  change IsOpenImmersion
    (pullback.snd C.openMap.left (S1926PointHom C T point).left)
  haveI : IsOpenImmersion C.openMap.left := C.openImmersion
  exact inferInstance

/-- **The stack map induced by the open immersion of a compactification datum is
representably an open immersion.** -/
noncomputable def S1926OpenImmersion (C : S1913AffineCompactification) :
    EtaleStackOpenImmersion C.S1913StackOpenMap where
  baseChange T point := S1926BaseChange C T point
  hasProperty T point := S1926Projection_isOpenImmersion C T point

/-- **S1913RepresentableOpenImmersion is closed**, for every compactification
datum. -/
theorem S1926RepresentableOpenImmersion (C : S1913AffineCompactification) :
    S1913RepresentableOpenImmersion C :=
  ⟨S1926OpenImmersion C⟩

/-- **The actual cusp from the scheme-level compactification datum alone.**  The
2-categorical input (b) is no longer assumed. -/
theorem S1926Cusp_of_compactification (C : S1913AffineCompactification) :
    Nonempty (OrbicurveBoundaryCusp S1726Orbicurve) :=
  C.S1913Cusp_of_compactification (S1926OpenImmersion C)

/-- The cusp from the two named S1913 inputs, with the second input supplied
here rather than assumed. -/
theorem S1926Cusp_of_inputs (C : S1913AffineCompactification) :
    Nonempty (OrbicurveBoundaryCusp S1726Orbicurve) :=
  S1913Cusp_of_inputs C (S1926OpenImmersion C)

/-! ## 6. Target-locked checks and axiom audit -/

#check @S1926PointHom
#check @S1926PullbackScheme
#check @S1926ToSource
#check @S1926Projection
#check @S1926IsPullback
#check @S1926Val
#check @S1926Val_strongTransOfHom
#check @S1926Val_vcomp
#check @S1926IsoOfValEq
#check @S1926SquareCommutesHom
#check @S1926CommutesVal
#check @S1926Square
#check @S1926TwoPullbackWitness
#check @S1926BaseChange
#check @S1926Projection_isOpenImmersion
#check @S1926OpenImmersion
#check @S1926RepresentableOpenImmersion
#check @S1926Cusp_of_compactification
#check @S1926Cusp_of_inputs

#print axioms S1926PointHom
#print axioms S1926IsPullback
#print axioms S1926Val_vcomp
#print axioms S1926IsoOfValEq
#print axioms S1926Square
#print axioms S1926TwoPullbackWitness
#print axioms S1926BaseChange
#print axioms S1926Projection_isOpenImmersion
#print axioms S1926OpenImmersion
#print axioms S1926RepresentableOpenImmersion
#print axioms S1926Cusp_of_compactification

end LeanFormal.IUT.XiFPaper.S1926RepresentableOpenImmersionActual