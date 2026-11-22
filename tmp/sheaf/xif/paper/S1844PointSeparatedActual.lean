/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors / S1844
-/
import tmp.sheaf.xif.paper.S1843SourceAllPointsActual

/-!
# S1844: point separation of the identity-point atlas, by full stack geometry -- and
why the recorded presentation data does not force it

## The question

S1841 isolated the first missing statement of the affine representability of a
cover source,

    S1841FirstMissing : for every cover A, toSource : h_{S_A} -> A.source is a
                        quasi-equivalence,

equivalently the full 2-dimensional universal property of the recorded
identity-point base-change square (S1827, S1831, S1804).  S1843 rewrote it in
geometric form as

    S1843PointSeparated A : toSource is injective on test-scheme points, i.e.
      x ; toSource ~ y ; toSource implies x ~ y for all x y : h_U -> h_{S_A},
    S1843ToSourceRightCancel A : toSource is right-cancellable,

and proved it equivalent to S1841FirstMissing.

The question of this file is whether the *full* stack / atlas geometry --
`A.source.isStack`, the identity-point atlas `S_A -> A.source`, the finite etale
base-change presentations at all scheme points, 2-Yoneda and the uniqueness of
2-cells into a representable stack -- proves S1843PointSeparated / right
cancellation, or whether the recorded data is still too weak.

## What is proved here, unconditionally

1. **2-cell uniqueness for representable targets** (`S1844SubsingletonMod`): two
   2-cells between strong transformations into a representable etale stack are
   equal, because every component lands in a discrete category.  This is the
   "stack 2-cell uniqueness" available for the model `h_{S_A}`.

2. **2-Yoneda functoriality** (`S1844YComp`, `S1844YId`): the strong
   transformation induced by a composite scheme morphism is 2-isomorphic to the
   composite of the induced strong transformations, and the one induced by an
   identity is 2-isomorphic to the identity.  These are the tools that reduce
   statements about `toSource` to scheme-level computations.

3. **The target in scheme-point (2-Yoneda) form**
   (`S1844SchemePointSeparated`, `S1844PointSeparated_iff_schemePoints`,
   `S1844FirstMissing_iff_schemePoints`): S1843PointSeparated is *exactly* the
   injectivity of the atlas on scheme-valued points,
   `sigma ; toSource ~ tau ; toSource -> sigma = tau` for all scheme morphisms
   `sigma tau : U -> S_A`.  So the remaining content of affine representability
   is literally the statement that the atlas `S_A -> A.source` is injective on
   scheme points.

4. **REFUTATION of the uniform statement.**  The doubled affine cover
   `Q = Spec (R' x R')` of the identity point carries a 2-commutative square
   (`S1844Square`) in the actual bicategory of etale stacks over `S1726K`:

       P = h_Q --toX = h(projection)--> X = h_{Spec R'}
         |toY = h(projection)               | xToBase = id (the base point)
         v                                  v
       Y = h_{Spec R'} --yToBase = id--> Z = X.stack = h_{Spec R'},

   i.e. a square of exactly the shape of the identity-point presentation square
   of the *trivial* cover (source `h_{Spec R'}`, map the identity) whose
   "pullback scheme" is the enlarged affine cover `Spec (R' x R')` (the split
   degree-two cover of the base) with projection the diagonal
   `Spec (R' x R') -> Spec R'`.  For it:

   * all seven recorded fields of `TwoPullbackWitness` hold (`S1844Witness`):
     the lift is precomposition with the canonical section `Spec R' -> Spec (R' x R')`,
     and the two 2-cell equations hold by 2-cell uniqueness;
   * all four objects are actual etale stacks: the apex and the base are
     representable (`S1844Q_isStack`, `S1844Base_isStack`), and the target is the
     orbicurve stack `S1726Orbicurve` (`S1844Target_isStack`, S1726);
   * the apex is representable and the right leg is the identity -- precisely the
     situation S1831 flagged as not covered by S1801's constant-apex model;
   * nevertheless the cone comparison is *not* essentially surjective
     (`S1844EssSurj_fails : not S1827EssSurjOf S1844Square S1844Witness`), right
     cancellation fails (`S1844RightCancel_fails`), point separation fails
     (`S1844PointSeparation_fails`), and consequently no uniform schema over
     representable objects holds (`S1844RepresentableSchema_fails`).

   The obstruction is the non-identity swap `swap : R' x R' -> R' x R'`: it is an
   automorphism of the doubled cover over the base (`S1844swap_nabla`), it is
   not the identity (`S1844swap_ne`), but its composite with the projection is
   the same as the identity's.  The section `iota` and the identity give
   `S1844iota_nabla`; the composite `nabla ; iota` is the diagonal projection
   `(a,b) -> (a,a)`, which is what the recorded lift produces
   (`S1844Lift_eval`), and it is not the swap (`S1844nabla_iota_ne_swap`).

## Honest verdict

* S1843PointSeparated and S1843ToSourceRightCancel are *not* consequences of:
  the stack condition on all objects involved, representability of the apex and
  of the base, the identity right leg, 2-Yoneda, or 2-cell uniqueness of the
  model.  All of these hold in the countermodel above.  Hence there is no
  uniform argument from the recorded weak-witness presentation data plus that
  geometry: the missing input is genuinely the *full* 2-dimensional universal
  property of the identity-point presentation square (equivalently, that its
  "pullback scheme" is the actual fiber), exactly as S1841/S1831 concluded from
  the other side.

* What this file does *not* do: it does not construct a cover
  (`OrbicurveFiniteEtaleCover`) -- the tree has no construction of
  `EtaleStackFiniteEtaleMorphism` at all -- so the statement
  `forall A, S1843PointSeparated A` is not literally refuted; what is refuted
  is the uniform schema for squares with representable apex and actual stack
  objects, in the exact shape of the identity-point presentation square.  The
  finite-etaleness of the projections is *not* used (and not formalised) here:
  the recorded `TwoPullbackWitness` does not contain it either, and the
  countermodel shows that adding the pullback scheme without the full universal
  property loses point separation.

* Consequence for the project: the definition of
  `EtaleStackBaseChangePresentation` (a weak two-pullback witness) admits
  "enlarged" presentations which are not the genuine pullback; closing
  S1841FirstMissing therefore requires either strengthening that definition to
  the full 2-dimensional universal property, or a geometric theorem that the
  recorded identity-point presentation is a full 2-pullback for the actual
  cover -- which is the target itself.

No sorry, no new axiom, no Shrink, ULift or PUnit, and no fake 2-cell or
equivalence is introduced.  The axiom footprint is propext, Classical.choice and
Quot.sound; see the audit block at the end of the file.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual

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
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1841SourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1843SourceAllPointsActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

/-! ## 1. Two-cells into a representable etale stack are unique -/

/-- Two-cells in Cat between functors into a discrete category are unique. -/
instance S1844SubsingletonHom2Discrete {C : Cat.{0, 0}} {A : Type}
    (G H : C ⟶ Cat.of (Discrete A)) : Subsingleton (G ⟶ H) := by
  constructor
  intro a b
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- Every component of a strong transformation into a representable etale stack
lands in a discrete category, so the 2-cells between two such strong
transformations are unique.  This is the 2-cell uniqueness of a stack whose
target is a sheaf. -/
theorem S1844SubsingletonMod {W : EtaleStackPseudofunctor S1726K}
    {Q : SchemeOverField S1726K}
    (a b : Pseudofunctor.StrongTrans W (S1743Y Q)) : Subsingleton (a ⟶ b) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (S1844SubsingletonHom2Discrete (a.app U) (b.app U)).elim (m.as.app U) (n.as.app U)

/-! ## 2. Functoriality of the 2-Yoneda construction -/

/-- The strong transformation induced by a composite scheme morphism is
2-isomorphic to the composite of the induced strong transformations. -/
noncomputable def S1844YComp {S T U : SchemeOverField S1726K}
    (f : S ⟶ T) (g : T ⟶ U) :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) f)
        (S1742StrongTransOfHom (F := S1726K) g))
      (S1742StrongTransOfHom (F := S1726K) (f ≫ g)) := by
  have h1 : Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1726K) f)
      (S1742StrongTransOfHom (F := S1726K) g))
      (S1742StrongTransOfHom (F := S1726K)
        (S1743YonedaEval S U (Pseudofunctor.StrongTrans.vcomp
          (S1742StrongTransOfHom (F := S1726K) f)
          (S1742StrongTransOfHom (F := S1726K) g)))) :=
    (S1742StrongTransIsoOfHom (F := S1726K) _).symm
  have h2 : S1743YonedaEval S U (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1726K) f)
      (S1742StrongTransOfHom (F := S1726K) g)) = f ≫ g := by
    rw [S1743YonedaEval_vcomp,
      show S1743YonedaEval S T (S1742StrongTransOfHom (F := S1726K) f) = f from
        S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) f,
      show S1743YonedaEval T U (S1742StrongTransOfHom (F := S1726K) g) = g from
        S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) g]
  exact h1.trans (eqToIso (congrArg (S1742StrongTransOfHom (F := S1726K)) h2))

/-- The representable strong transformation of an identity is 2-isomorphic to
the identity strong transformation. -/
noncomputable def S1844YId (S : SchemeOverField S1726K) :
    Iso (S1742StrongTransOfHom (F := S1726K) (𝟙 S))
      (Pseudofunctor.StrongTrans.id (S1743Y S)) :=
  S1742StrongTransIsoOfHom (F := S1726K) (Pseudofunctor.StrongTrans.id (S1743Y S))

/-! ## 3. The doubled affine cover of the identity point -/

/-- The ring R' x R' of the doubled cover of the identity point. -/
abbrev S1844A : Type := S1726CoordinateRing × S1726CoordinateRing

/-- The K-algebra structure morphism of the doubled ring. -/
def S1844delta : S1726K →+* S1844A :=
  (algebraMap S1726K S1726CoordinateRing).prod
    (algebraMap S1726K S1726CoordinateRing)

/-- The diagonal R' -> R' x R'. -/
def S1844diag : S1726CoordinateRing →+* S1844A :=
  (RingHom.id _).prod (RingHom.id _)

/-- The first projection R' x R' -> R'. -/
def S1844pr1 : S1844A →+* S1726CoordinateRing := RingHom.fst _ _

/-- The swap of R' x R'. -/
def S1844swap : S1844A →+* S1844A := RingEquiv.prodComm.toRingHom

theorem S1844swap_delta : S1844swap.comp S1844delta = S1844delta := rfl

theorem S1844diag_delta :
    S1844diag.comp (algebraMap S1726K S1726CoordinateRing) = S1844delta := rfl

theorem S1844pr1_delta :
    S1844pr1.comp S1844delta = algebraMap S1726K S1726CoordinateRing := rfl

theorem S1844pr1_diag : S1844pr1.comp S1844diag = RingHom.id _ := rfl

theorem S1844swap_diag : S1844swap.comp S1844diag = S1844diag := rfl

/-- The doubled cover Spec (R' x R') as a scheme over Spec K. -/
abbrev S1844Q : SchemeOverField S1726K :=
  Over.mk (Spec.map (CommRingCat.ofHom S1844delta))

/-- The projection Spec (R' x R') -> Spec R' onto the identity point. -/
noncomputable def S1844nabla : S1844Q ⟶ S1726AffineOver :=
  Over.homMk (Spec.map (CommRingCat.ofHom S1844diag)) (by
    change Spec.map (CommRingCat.ofHom S1844diag) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S1726K S1726CoordinateRing)) =
      Spec.map (CommRingCat.ofHom S1844delta)
    rw [← Spec.map_comp (CommRingCat.ofHom (algebraMap S1726K S1726CoordinateRing))
      (CommRingCat.ofHom S1844diag)]
    exact congrArg Spec.map (by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact congrArg (fun f => f a) S1844diag_delta))

/-- The section Spec R' -> Spec (R' x R') of the projection. -/
noncomputable def S1844iota : S1726AffineOver ⟶ S1844Q :=
  Over.homMk (Spec.map (CommRingCat.ofHom S1844pr1)) (by
    change Spec.map (CommRingCat.ofHom S1844pr1) ≫
      Spec.map (CommRingCat.ofHom S1844delta) =
      Spec.map (CommRingCat.ofHom (algebraMap S1726K S1726CoordinateRing))
    rw [← Spec.map_comp (CommRingCat.ofHom S1844delta) (CommRingCat.ofHom S1844pr1)]
    exact congrArg Spec.map (by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact congrArg (fun f => f a) S1844pr1_delta))

/-- The swap of the two components, as an automorphism of the doubled cover over
the base. -/
noncomputable def S1844swapMap : S1844Q ⟶ S1844Q :=
  Over.homMk (Spec.map (CommRingCat.ofHom S1844swap)) (by
    change Spec.map (CommRingCat.ofHom S1844swap) ≫
      Spec.map (CommRingCat.ofHom S1844delta) =
      Spec.map (CommRingCat.ofHom S1844delta)
    rw [← Spec.map_comp (CommRingCat.ofHom S1844delta) (CommRingCat.ofHom S1844swap)]
    exact congrArg Spec.map (by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact congrArg (fun f => f a) S1844swap_delta))

/-- The section is a section of the projection. -/
theorem S1844iota_nabla : S1844iota ≫ S1844nabla = 𝟙 S1726AffineOver := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom S1844pr1) ≫ Spec.map (CommRingCat.ofHom S1844diag) =
    𝟙 (Spec (CommRingCat.of S1726CoordinateRing))
  rw [← Spec.map_comp (CommRingCat.ofHom S1844diag) (CommRingCat.ofHom S1844pr1)]
  rw [show (CommRingCat.ofHom S1844diag) ≫ (CommRingCat.ofHom S1844pr1) =
      𝟙 (CommRingCat.of S1726CoordinateRing) from by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact congrArg (fun f => f a) S1844pr1_diag]
  exact Spec.map_id _

/-- The swap does not change the projection. -/
theorem S1844swap_nabla : S1844swapMap ≫ S1844nabla = S1844nabla := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom S1844swap) ≫ Spec.map (CommRingCat.ofHom S1844diag) =
    Spec.map (CommRingCat.ofHom S1844diag)
  rw [← Spec.map_comp (CommRingCat.ofHom S1844diag) (CommRingCat.ofHom S1844swap)]
  exact congrArg Spec.map (by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact congrArg (fun f => f a) S1844swap_diag)

/-! ## 4. R' is nontrivial -/

/-- The identity point of the affine model is a rational point of the curve. -/
theorem S1844originEquation : S1726Curve.toAffine.Equation 0 0 :=
  WeierstrassCurve.Affine.equation_zero.mpr S1726Curve_a₆

/-- R' is a nontrivial ring. -/
theorem S1844nontrivialRing : Nontrivial S1726CoordinateRing := by
  refine ⟨0, 1, ?_⟩
  intro h
  have h' : S1726PointAlgHom (0 : S1726K) (0 : S1726K) S1844originEquation
        (1 : S1726CoordinateRing) =
      S1726PointAlgHom (0 : S1726K) (0 : S1726K) S1844originEquation 0 := by rw [h]
  rw [map_one, map_zero] at h'
  exact zero_ne_one h'.symm

instance S1844nontrivialRingInst : Nontrivial S1726CoordinateRing := S1844nontrivialRing

/-- The swap is not the identity automorphism of the doubled cover. -/
theorem S1844swap_ne : (𝟙 S1844Q) ≠ S1844swapMap := by
  intro h
  have hleft : Over.Hom.left (𝟙 S1844Q) = Over.Hom.left S1844swapMap :=
    congrArg Over.Hom.left h
  have hspec0 : (𝟙 (Spec (CommRingCat.of S1844A))) =
      Spec.map (CommRingCat.ofHom S1844swap) := hleft
  have hspec : Spec.map (𝟙 (CommRingCat.of S1844A)) =
      Spec.map (CommRingCat.ofHom S1844swap) := by
    rw [Spec.map_id]
    exact hspec0
  have hring : (CommRingCat.ofHom (RingHom.id S1844A)) =
      CommRingCat.ofHom S1844swap := Spec.map_injective hspec
  have hR : (RingHom.id S1844A) = S1844swap := by
    simpa only [CommRingCat.hom_ofHom] using congrArg CommRingCat.Hom.hom hring
  have hpt := congrArg (fun f : S1844A →+* S1844A => f ((1, 0))) hR
  simp [S1844swap] at hpt

/-! ## 5. The square and its recorded witness -/

/-- The model square: the apex is the representable stack of the doubled cover,
both legs are the projection, and the right leg at the base is the identity (the
identity point of the representable base). -/
noncomputable def S1844Square :
    EtalePseudofunctorSquare (S1743Y S1844Q) (S1743Y S1726AffineOver)
      (S1743Y S1726AffineOver) (S1726Orbicurve.stack.fiber) where
  toX := S1742StrongTransOfHom (F := S1726K) S1844nabla
  toY := S1742StrongTransOfHom (F := S1726K) S1844nabla
  xToBase := S1733BasePoint
  yToBase := S1733BasePoint
  commutes := Iso.refl _

/-- The lift of a cone: precomposition with the section of the projection. -/
noncomputable def S1844Lift {W : EtaleStackPseudofunctor S1726K}
    (c : S1844Square.Cone W) :
    Pseudofunctor.StrongTrans W (S1743Y S1844Q) :=
  Pseudofunctor.StrongTrans.vcomp c.toX
    (S1742StrongTransOfHom (F := S1726K) S1844iota)

/-- The composite of the section with the projection is the identity. -/
noncomputable def S1844IotaNablaIso :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) S1844iota)
        (S1742StrongTransOfHom (F := S1726K) S1844nabla))
      (Pseudofunctor.StrongTrans.id (S1743Y S1726AffineOver)) :=
  (S1844YComp S1844iota S1844nabla).trans
    ((eqToIso (congrArg (S1742StrongTransOfHom (F := S1726K)) S1844iota_nabla)).trans
      (S1844YId S1726AffineOver))

/-- The two legs of a cone into the model are 2-isomorphic. -/
noncomputable def S1844ConeLegsIso {W : EtaleStackPseudofunctor S1726K}
    (c : S1844Square.Cone W) : Iso c.toX c.toY :=
  (S1756RightUnitorIso c.toX).symm.trans
    (c.commutes.trans (S1756RightUnitorIso c.toY))

/-- The composite of the lift with the first projection. -/
noncomputable def S1844LiftToX {W : EtaleStackPseudofunctor S1726K}
    (c : S1844Square.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1844Lift c) S1844Square.toX) c.toX :=
  (S1756AssociatorIso c.toX
      (S1742StrongTransOfHom (F := S1726K) S1844iota)
      (S1742StrongTransOfHom (F := S1726K) S1844nabla)).trans
    ((S1756WhiskerLeftIso c.toX
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) S1844iota)
        (S1742StrongTransOfHom (F := S1726K) S1844nabla))
      (Pseudofunctor.StrongTrans.id (S1743Y S1726AffineOver))
      S1844IotaNablaIso).trans
      (S1756RightUnitorIso c.toX))

/-- The composite of the lift with the second projection. -/
noncomputable def S1844LiftToY {W : EtaleStackPseudofunctor S1726K}
    (c : S1844Square.Cone W) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S1844Lift c) S1844Square.toY) c.toY :=
  (S1756AssociatorIso c.toX
      (S1742StrongTransOfHom (F := S1726K) S1844iota)
      (S1742StrongTransOfHom (F := S1726K) S1844nabla)).trans
    ((S1756WhiskerLeftIso c.toX
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) S1844iota)
        (S1742StrongTransOfHom (F := S1726K) S1844nabla))
      (Pseudofunctor.StrongTrans.id (S1743Y S1726AffineOver))
      S1844IotaNablaIso).trans
      ((S1756RightUnitorIso c.toX).trans (S1844ConeLegsIso c)))

/-- **The recorded weak two-pullback witness of the model square.** -/
noncomputable def S1844Witness : S1844Square.TwoPullbackWitness where
  lift _ c := S1844Lift c
  liftToX _ c := S1844LiftToX c
  liftToY _ c := S1844LiftToY c
  liftTwoCell _ _ _ m :=
    Pseudofunctor.StrongTrans.whiskerRight m.toX
      (S1742StrongTransOfHom (F := S1726K) S1844iota)
  liftTwoCell_toX _ _ _ _ := (S1844SubsingletonMod _ _).allEq _ _
  liftTwoCell_toY _ _ _ _ := (S1844SubsingletonMod _ _).allEq _ _
  twoCell_ext _ first second alpha beta _ _ :=
    (S1844SubsingletonMod first second).allEq alpha beta

/-! ## 6. Right cancellation fails for the model square -/

/-- The identity of the model and the swap have the same composite with the
projection. -/
theorem S1844_same_composite :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id (S1743Y S1844Q)) S1844Square.toX)
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) S1844swapMap) S1844Square.toX)) := by
  refine ⟨(S1756LeftUnitorIso (S1742StrongTransOfHom (F := S1726K) S1844nabla)).trans
    ((eqToIso (congrArg (fun f => S1742StrongTransOfHom (F := S1726K) f)
      S1844swap_nabla.symm)).trans
      (S1844YComp S1844swapMap S1844nabla).symm)⟩

/-- **Right cancellation fails for the recorded weak-witness data**, even though
every object of the square is an actual etale stack (a representable one), the
apex is representable, and the right leg is the identity. -/
theorem S1844RightCancel_fails : ¬ S1843RightCancelOf S1844Square S1844Witness := by
  intro h
  obtain ⟨e⟩ := h (S1743Y S1844Q)
    (Pseudofunctor.StrongTrans.id (S1743Y S1844Q))
    (S1742StrongTransOfHom (F := S1726K) S1844swapMap) S1844_same_composite
  have hev := S1743YonedaEval_congr_iso S1844Q S1844Q e
  rw [show S1743YonedaEval S1844Q S1844Q
        (Pseudofunctor.StrongTrans.id (S1743Y S1844Q)) = 𝟙 S1844Q from rfl,
    show S1743YonedaEval S1844Q S1844Q
        (S1742StrongTransOfHom (F := S1726K) S1844swapMap) = S1844swapMap from
      S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) S1844swapMap] at hev
  exact S1844swap_ne hev

/-- The same failure in point-separation (injectivity) form. -/
theorem S1844PointSeparation_fails :
    ¬ (∀ x y : Pseudofunctor.StrongTrans (S1743Y S1844Q) (S1743Y S1844Q),
        Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp x S1844Square.toX)
          (Pseudofunctor.StrongTrans.vcomp y S1844Square.toX)) →
        Nonempty (Iso x y)) := by
  intro h
  obtain ⟨e⟩ := h (Pseudofunctor.StrongTrans.id (S1743Y S1844Q))
    (S1742StrongTransOfHom (F := S1726K) S1844swapMap) S1844_same_composite
  have hev := S1743YonedaEval_congr_iso S1844Q S1844Q e
  rw [show S1743YonedaEval S1844Q S1844Q
        (Pseudofunctor.StrongTrans.id (S1743Y S1844Q)) = 𝟙 S1844Q from rfl,
    show S1743YonedaEval S1844Q S1844Q
        (S1742StrongTransOfHom (F := S1726K) S1844swapMap) = S1844swapMap from
      S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) S1844swapMap] at hev
  exact S1844swap_ne hev


/-! ## 7. The atlas in scheme-point (2-Yoneda) form -/

/-- **Point separation of the comparison in scheme-point form**: two scheme
points of the affine model whose images under the identity-point comparison are
2-isomorphic are equal.  By 2-Yoneda this is the literal injectivity of the
atlas on scheme-valued points. -/
def S1844SchemePointSeparated (A : S1728Cover) : Prop :=
  ∀ (U : SchemeOverField S1726K) (σ τ : U ⟶ S1733Model A),
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) σ) (S1756ToSource A))
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) τ) (S1756ToSource A))) →
    σ = τ

/-- Point separation of S1843 is exactly scheme-point injectivity of the atlas. -/
theorem S1844PointSeparated_iff_schemePoints (A : S1728Cover) :
    S1843PointSeparated A ↔ S1844SchemePointSeparated A := by
  constructor
  · intro h U σ τ he
    have h' := h U (S1742StrongTransOfHom (F := S1726K) σ)
      (S1742StrongTransOfHom (F := S1726K) τ) he
    obtain ⟨e⟩ := h'
    have hev := S1743YonedaEval_congr_iso U (S1733Model A) e
    rw [show S1743YonedaEval U (S1733Model A)
          (S1742StrongTransOfHom (F := S1726K) σ) = σ from
        S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) σ,
      show S1743YonedaEval U (S1733Model A)
          (S1742StrongTransOfHom (F := S1726K) τ) = τ from
        S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) τ] at hev
    exact hev
  · intro h U x y he
    have hx : Iso (S1742StrongTransOfHom (F := S1726K)
        (S1743YonedaEval U (S1733Model A) x)) x :=
      S1742StrongTransIsoOfHom (F := S1726K) x
    have hy : Iso (S1742StrongTransOfHom (F := S1726K)
        (S1743YonedaEval U (S1733Model A) y)) y :=
      S1742StrongTransIsoOfHom (F := S1726K) y
    have he' : Nonempty (Iso
        (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom (F := S1726K)
          (S1743YonedaEval U (S1733Model A) x)) (S1756ToSource A))
        (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom (F := S1726K)
          (S1743YonedaEval U (S1733Model A) y)) (S1756ToSource A))) := by
      refine ⟨(S1756WhiskerRightIso _ _ (S1756ToSource A) hx).trans
        ((he.some).trans
          (S1756WhiskerRightIso _ _ (S1756ToSource A) hy).symm)⟩
    have hEq : S1743YonedaEval U (S1733Model A) x =
        S1743YonedaEval U (S1733Model A) y := h U _ _ he'
    exact ⟨hx.symm.trans
      ((eqToIso (congrArg (S1742StrongTransOfHom (F := S1726K)) hEq)).trans hy)⟩

/-- The exact first missing, in the scheme-point injectivity form of the atlas. -/
theorem S1844FirstMissing_iff_schemePoints :
    S1841FirstMissing ↔ ∀ A : S1728Cover, S1844SchemePointSeparated A :=
  S1843FirstMissing_iff_pointSeparated.trans
    (forall_congr' fun A => S1844PointSeparated_iff_schemePoints A)

/-- Right cancellation in the scheme-point injectivity form. -/
theorem S1844RightCancel_iff_schemePoints :
    S1841FirstMissing ↔ ∀ A : S1728Cover, S1843ToSourceRightCancel A :=
  S1843FirstMissing_iff_rightCancel

/-! ## 8. The apex of the model square is an actual etale stack -/

/-- The apex of the model square is an actual etale stack: the representable
pseudofunctor of the doubled cover is a stack for the etale topology. -/
theorem S1844Q_isStack :
    (S1743Y S1844Q).IsStack (Iut.SchemeOverField.etaleTopology S1726K) := by
  have hP : Presieve.IsSheaf (Iut.SchemeOverField.etaleTopology S1726K)
      (yoneda.obj S1844Q) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (representableEtalePresheaf_isSheaf (F := S1726K) S1844Q)
  change (discretePseudo (C := Iut.SchemeOverField S1726K)
    (yoneda.obj S1844Q)).IsStack (Iut.SchemeOverField.etaleTopology S1726K)
  exact DiscreteSheafStack.discretePseudo_isStack (P := yoneda.obj S1844Q) hP

/-- The base of the model square is an actual etale stack. -/
theorem S1844Base_isStack :
    (S1743Y S1726AffineOver).IsStack (Iut.SchemeOverField.etaleTopology S1726K) :=
  S1726RepresentableIsStack

/-- The orbicurve base of the model square is an actual etale stack. -/
theorem S1844Target_isStack :
    S1726Orbicurve.stack.fiber.IsStack (Iut.SchemeOverField.etaleTopology S1726K) :=
  S1726Orbicurve_stack_isStack

/-- The ring endomorphism of the doubled cover given by the projection followed by
the diagonal, (a,b) |-> (a,a). -/
def S1844rho : S1844A →+* S1844A := S1844diag.comp S1844pr1

theorem S1844rho_ne_swap : S1844rho ≠ S1844swap := by
  intro h
  have h2 : S1844rho ((0, 1)) = S1844swap ((0, 1)) :=
    congrArg (fun f : S1844A →+* S1844A => f ((0, 1))) h
  have h3 : (((0 : S1726CoordinateRing), (0 : S1726CoordinateRing)) : S1844A) =
      (((1 : S1726CoordinateRing), (0 : S1726CoordinateRing)) : S1844A) := h2
  have h1 : (0 : S1726CoordinateRing) = 1 := congrArg Prod.fst h3
  exact zero_ne_one h1

/-- The composite of the projection with the section, as an endomorphism of the
doubled cover, is not the swap. -/
theorem S1844nabla_iota_ne_swap : S1844nabla ≫ S1844iota ≠ S1844swapMap := by
  intro h
  have hleft : Over.Hom.left S1844swapMap =
      Over.Hom.left (S1844nabla ≫ S1844iota) := congrArg Over.Hom.left h.symm
  rw [Over.comp_left] at hleft
  have h2 : Spec.map (CommRingCat.ofHom S1844swap) =
      Spec.map (CommRingCat.ofHom S1844diag) ≫
        Spec.map (CommRingCat.ofHom S1844pr1) := hleft
  have hstep : Spec.map (CommRingCat.ofHom S1844diag) ≫
      Spec.map (CommRingCat.ofHom S1844pr1) =
        Spec.map (CommRingCat.ofHom S1844rho) := by
    rw [← Spec.map_comp (CommRingCat.ofHom S1844pr1) (CommRingCat.ofHom S1844diag)]
    exact congrArg Spec.map (CommRingCat.ofHom_comp S1844pr1 S1844diag).symm
  rw [hstep] at h2
  have hring : CommRingCat.ofHom S1844swap = CommRingCat.ofHom S1844rho :=
    Spec.map_injective h2
  have hR : S1844swap = S1844rho := by
    simpa only [CommRingCat.hom_ofHom] using congrArg CommRingCat.Hom.hom hring
  exact S1844rho_ne_swap hR.symm

/-! ## 10. The essential-surjectivity half fails for the model square -/

/-- The tautological cone of the model square, with apex the model itself. -/
noncomputable def S1844TautologicalCone : S1844Square.Cone (S1743Y S1844Q) where
  toX := S1742StrongTransOfHom (F := S1726K) S1844nabla
  toY := S1742StrongTransOfHom (F := S1726K) S1844nabla
  commutes := Iso.refl _

/-- The swap agrees with the tautological cone on the first leg. -/
theorem S1844TautologicalCone_fst :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) S1844swapMap) S1844Square.toX)
      S1844TautologicalCone.toX) :=
  ⟨(S1844YComp S1844swapMap S1844nabla).trans
    (eqToIso (congrArg (S1742StrongTransOfHom (F := S1726K)) S1844swap_nabla))⟩

/-- The swap agrees with the tautological cone on the second leg. -/
theorem S1844TautologicalCone_snd :
    Nonempty (Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1726K) S1844swapMap) S1844Square.toY)
      S1844TautologicalCone.toY) :=
  ⟨(S1844YComp S1844swapMap S1844nabla).trans
    (eqToIso (congrArg (S1742StrongTransOfHom (F := S1726K)) S1844swap_nabla))⟩

/-- The lift of the tautological cone evaluates to the projection composed with
the section. -/
theorem S1844Lift_eval :
    S1743YonedaEval S1844Q S1844Q
      (S1844Witness.lift (S1743Y S1844Q) S1844TautologicalCone) =
        S1844nabla ≫ S1844iota := by
  show S1743YonedaEval S1844Q S1844Q
    (Pseudofunctor.StrongTrans.vcomp S1844TautologicalCone.toX
      (S1742StrongTransOfHom (F := S1726K) S1844iota)) = _
  rw [S1743YonedaEval_vcomp,
    show S1743YonedaEval S1844Q S1726AffineOver S1844TautologicalCone.toX =
        S1844nabla from
      S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) S1844nabla,
    show S1743YonedaEval S1726AffineOver S1844Q
        (S1742StrongTransOfHom (F := S1726K) S1844iota) = S1844iota from
      S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) S1844iota]

/-- **The essential-surjectivity half of the 2-universal property fails** for the
model square: the swap is not 2-isomorphic to the lift of the tautological cone,
although its two projections agree with the cone's. -/
theorem S1844EssSurj_fails : ¬ S1827EssSurjOf S1844Square S1844Witness := by
  intro h
  obtain ⟨e⟩ := h (S1743Y S1844Q) S1844TautologicalCone
    (S1742StrongTransOfHom (F := S1726K) S1844swapMap)
    S1844TautologicalCone_fst S1844TautologicalCone_snd
  have hev := S1743YonedaEval_congr_iso S1844Q S1844Q e
  rw [show S1743YonedaEval S1844Q S1844Q
        (S1742StrongTransOfHom (F := S1726K) S1844swapMap) = S1844swapMap from
      S1742HomOfStrongTrans_strongTransOfHom (F := S1726K) S1844swapMap,
    S1844Lift_eval] at hev
  exact S1844nabla_iota_ne_swap hev.symm

/-- **The schema fails already for squares whose four objects are representable
etale stacks**: no uniform argument from the recorded weak-witness fields can
produce right cancellation for such a square. -/
theorem S1844RepresentableSchema_fails :
    ¬ (∀ (Q X Y Z : SchemeOverField S1726K)
        (sq : EtalePseudofunctorSquare (S1743Y Q) (S1743Y X) (S1743Y Y) (S1743Y Z))
        (w : sq.TwoPullbackWitness), S1843RightCancelOf sq w) := by
  intro h
  exact S1844RightCancel_fails
    (h S1844Q S1726AffineOver S1726AffineOver S1726AffineOver S1844Square S1844Witness)

/-! ## 11. Checks and axiom audit -/

#check S1844SubsingletonMod
#check S1844YComp
#check S1844YId
#check S1844Q
#check S1844nabla
#check S1844iota
#check S1844swapMap
#check S1844IotaNablaIso
#check S1844Square
#check S1844Witness
#check S1844RightCancel_fails
#check S1844PointSeparation_fails
#check S1844EssSurj_fails
#check S1844RepresentableSchema_fails
#check S1844SchemePointSeparated
#check S1844PointSeparated_iff_schemePoints
#check S1844FirstMissing_iff_schemePoints
#check S1844Q_isStack
#check S1844Base_isStack
#check S1844Target_isStack

#print axioms S1844SubsingletonMod
#print axioms S1844YComp
#print axioms S1844YId
#print axioms S1844IotaNablaIso
#print axioms S1844swap_ne
#print axioms S1844RightCancel_fails
#print axioms S1844PointSeparation_fails
#print axioms S1844EssSurj_fails
#print axioms S1844RepresentableSchema_fails
#print axioms S1844PointSeparated_iff_schemePoints
#print axioms S1844FirstMissing_iff_schemePoints
#print axioms S1844Q_isStack
#print axioms S1844Base_isStack
#print axioms S1844Target_isStack

end LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
