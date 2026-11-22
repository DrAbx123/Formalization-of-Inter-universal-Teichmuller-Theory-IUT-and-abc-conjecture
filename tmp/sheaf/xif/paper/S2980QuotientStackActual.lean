/-
# S2980: the actual sign-action diagram `D` and the first blocked input of `W`

Deep-audit group B asked for the corrected quotient stack
`D : Pseudofunctor SignActionIndex (EtaleStackPseudofunctor F)` together with
`atBase`, `generator_identification`, and
`W : S2870QuotientWitnessData S2882A6Q hQ (S2869SignAction D atBase gen)`.

This file records what is actually constructible and what is not.

## Constructed here (no sorry, no axiom, no placeholder)

* `S2980D`: the sign-action pseudofunctor on the A6 scheme
  `S2844X`, with `D.obj signActionObject = S2855HyperbolicOrbicurve.stack.fiber`
  (the representable etale stack of the curve) and `D.map signActionGenerator`
  the actual elliptic involution `S2857StackAuto alphaOverS2844`.
  All higher coherences are discharged by the 2-cell subsingleton of the
  representable stack (its value categories are discrete).
* `S2980AtBase`: the identity adjoint equivalence to
  `S2855HyperbolicOrbicurve.stack.fiber`.
* `S2980GeneratorIdentification`: the unitor 2-isomorphism identifying the
  generator with `S2857StackAuto alphaOverS2844`.
* `S2980A`: the resulting actual `Iut.OrbicurveSignAction
  S2855HyperbolicOrbicurve` (the `S2869SignAction` consumer).

The object `D` with the type demanded by the corrected core is therefore
NOT missing; it is the *sign-action diagram on the source curve X_F*, not the
quotient stack `[X_F/sign]`.  The quotient object is the separate input
`Q` / its stackification.

## The first blocked input of W

`W` has type `S2870QuotientWitnessData S2882A6Q hQ A`, whose first argument
`hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology F)` is not merely
unproved: it is REFUTED in the tree.

* `S2975bA6QPresheafHomSheaf.S2975b_not_isStack` proves
  `not S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology K)` by the empty-base
  obstruction: the hom presheaf of `S2882A6Q` is not a sheaf on the empty
  scheme, so `S2882A6Q` is not even a prestack.
* `S2993A6QIsStackNoGo.S2993_not_isStack` is the same statement repeated
  (and `S2993_not_isPrestack` the prestack version).

Consequently `S2870QuotientWitnessData S2882A6Q hQ A` is vacuous for every
`A`: there is no `hQ`.  `S2980NotHQ` below is the machine-checked
re-export, and `S2980W_vacuous` derives `False` from any hypothetical
`W`.

## Exact first Lean error when attempting W

Attempting to synthesize the instance directly

```lean
example : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F) := by
  infer_instance
```

fails with

```
error: failed to synthesize instance of type class
  Pseudofunctor.IsStack S2882A6Q (SchemeOverField.etaleTopology S2847A6.F)
```

With `hQ` granted as a hypothesis, the first field of `W` is

```
quotient : Iut.OrbicurveSignInvariantMorphism A (S2891CF hQ)
```

and it has no supplier in the tree (the canonical map to the pointwise
action groupoid is not a stack quotient and `S2891CF hQ` does not exist
without `hQ`); the universal-property field `quotientWitness` is a further
separate obligation.

## Corrected route (not constructed here)

The corrected object has to be a stackification `Q'` of the pointwise
prestack `S2882A6Q` (the torsor stack `[X_F/SignGroup]`), with an
`IsStack Q'` proof and a fiberwise equivalence `Q' = S2882A6Q`, and
`W'` has to be stated for `Q'` rather than for `S2882A6Q`.  S2994/S2996
contain only specifications and a proposition-level target for that object;
no `Q'` is constructed in the tree.
-/

import tmp.sheaf.xif.paper.S2870A6CFPathAudit
import tmp.sheaf.xif.paper.S2882A6PointwisePseudofunctorActual
import tmp.sheaf.xif.paper.S2857StackAutoForA6Actual
import tmp.sheaf.xif.paper.S2993A6QIsStackNoGo

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2869A6CoreWithGenericQuotient
open LeanFormal.IUT.XiFPaper.S2870A6CFPathAudit
open LeanFormal.IUT.XiFPaper.S2993A6QIsStackNoGo
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2980QuotientStackActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-! ## 1. The sign action on the A6 curve, as a pseudofunctor -/

/-- The A6 scheme, named over the base field of the corrected core. -/
abbrev S2980X : Iut.SchemeOverField S2847A6.F := S2844X

/-- The representable etale stack of the A6 curve; this is definitionally the
fiber of `S2855HyperbolicOrbicurve`. -/
abbrev S2980Q : Iut.EtaleStackPseudofunctor S2847A6.F :=
  S1742YS (F := S2847A6.F) S2980X

/-- The fiber of the A6 hyperbolic orbicurve is the representable stack of
`S2844X`. -/
theorem S2980FiberEq : S2855HyperbolicOrbicurve.stack.fiber = S2980Q := rfl

/-- Multiplication in the sign group, used to avoid typeclass elaboration on
the abstract morphism types of `SignActionIndex`. -/
def S2980Mul (x y : Iut.SignGroup) : Iut.SignGroup := x * y

/-- The underlying sign-group element of a composed index morphism. -/
theorem S2980SigMap_comp_as {a b c : Iut.SignActionIndex} (f : a ⟶ b) (g : b ⟶ c) :
    ((f ≫ g).as : Iut.SignGroup) =
      S2980Mul (g.as : Iut.SignGroup) (f.as : Iut.SignGroup) := by
  rw [LocallyDiscrete.comp_as, SingleObj.comp_as_mul]
  rfl

/-- The multiplication law of the scheme automorphism, in the order needed for
the strong-transformation composition. -/
theorem S2980Aut_mulS (x y : Iut.SignGroup) :
    S2882A6Aut (S2980Mul x y) = S2882A6Aut y ≫ S2882A6Aut x := by
  change S2882A6Aut (x * y) = S2882A6Aut y ≫ S2882A6Aut x
  rw [S2882A6Aut_mul]

/-- The scheme automorphism of a composed index morphism is the composite of the
automorphisms of the factors. -/
theorem S2980Aut_comp_as {a b c : Iut.SignActionIndex} (f : a ⟶ b) (g : b ⟶ c) :
    S2882A6Aut ((f ≫ g).as) = S2882A6Aut (f.as : Iut.SignGroup) ≫
      S2882A6Aut (g.as : Iut.SignGroup) := by
  rw [S2980SigMap_comp_as]
  exact S2980Aut_mulS (g.as) (f.as)

/-- The generator's underlying sign-group element. -/
theorem S2980SignGenAs : (Iut.signActionGenerator.as : Iut.SignGroup) =
    Multiplicative.ofAdd (1 : ZMod 2) := rfl

/-! ## 2. Two-cell subsingletons of the representable stack -/

theorem S2980NatTransSubsingleton {X Y : Cat.{0, 0}} (hY : IsDiscrete (Y : Type))
    (F G : X ⟶ Y) : Subsingleton (F ⟶ G) := by
  letI := hY
  constructor
  intro α β
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext Z
  exact Subsingleton.elim _ _

theorem S2980CatHomSubsingleton (U : LocallyDiscrete (Iut.SchemeOverField S2847A6.F)ᵒᵖ)
    (F G : S2980Q.obj U ⟶ S2980Q.obj U) : Subsingleton (F ⟶ G) :=
  S2980NatTransSubsingleton (Discrete.isDiscrete _) F G

/-- Every 2-cell between endomorphisms of the representable stack is trivial. -/
theorem S2980StrongTransSubsingleton
    (F G : Pseudofunctor.StrongTrans S2980Q S2980Q) : Subsingleton (F ⟶ G) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (S2980CatHomSubsingleton U (F.app U) (G.app U)).elim _ _

/-! ## 3. The diagram and its coherences -/

noncomputable def S2980SigMapOf (g : Iut.SignGroup) : S2980Q ⟶ S2980Q :=
  S1742StrongTransOfHom (F := S2847A6.F) (S2882A6Aut g)

noncomputable def S2980SigMap {a b : Iut.SignActionIndex} (f : a ⟶ b) : S2980Q ⟶ S2980Q :=
  S2980SigMapOf f.as

/-- The generator acts by the actual elliptic involution. -/
theorem S2980SigMap_gen :
    S2980SigMap Iut.signActionGenerator =
      S1742StrongTransOfHom (F := S2847A6.F) alphaOverS2844 := by
  change S1742StrongTransOfHom (F := S2847A6.F)
      (S2882A6Aut (Iut.signActionGenerator.as : Iut.SignGroup)) =
    S1742StrongTransOfHom (F := S2847A6.F) alphaOverS2844
  rw [S2980SignGenAs, S2882A6Aut_gen]

/-- Comparison of strong transformations with the same underlying scheme
morphism, via the 2-Yoneda round trip. -/
noncomputable def S2980IsoOfHomEq {eta theta : S2980Q ⟶ S2980Q}
    (h : S1742HomOfStrongTrans (F := S2847A6.F) eta =
      S1742HomOfStrongTrans (F := S2847A6.F) theta) : eta ≅ theta :=
  (S1742StrongTransIsoOfHom (F := S2847A6.F) eta).symm.trans
    (h.symm ▸ S1742StrongTransIsoOfHom (F := S2847A6.F) theta)

/-- Unit coherence: the identity index morphism acts by the identity. -/
noncomputable def S2980MapId (a : Iut.SignActionIndex) :
    S2980SigMap (𝟙 a) ≅ 𝟙 S2980Q := by
  have h : S2980SigMap (𝟙 a) = S2980SigMapOf (1 : Iut.SignGroup) := by
    change S2980SigMapOf (Discrete.as (𝟙 a)) = S2980SigMapOf (1 : Iut.SignGroup)
    rw [show Discrete.as (𝟙 a) = (1 : Iut.SignGroup) from by
      rw [LocallyDiscrete.id_as]
      rfl]
  rw [h]
  exact S1742StrongTransIsoOfHom (F := S2847A6.F) (Pseudofunctor.StrongTrans.id S2980Q)

/-- Composition coherence. -/
noncomputable def S2980MapComp {a b c : Iut.SignActionIndex}
    (f : a ⟶ b) (g : b ⟶ c) :
    S2980SigMap (f ≫ g) ≅ S2980SigMap f ≫ S2980SigMap g := by
  apply S2980IsoOfHomEq
  change S1742HomOfStrongTrans (F := S2847A6.F) (S2980SigMap (f ≫ g)) =
    S1742HomOfStrongTrans (F := S2847A6.F)
      (Pseudofunctor.StrongTrans.vcomp (S2980SigMap f) (S2980SigMap g))
  rw [S1742HomOfStrongTrans_vcomp]
  change S1742HomOfStrongTrans (F := S2847A6.F)
      (S1742StrongTransOfHom (F := S2847A6.F) (S2882A6Aut ((f ≫ g).as))) =
    S1742HomOfStrongTrans (F := S2847A6.F)
        (S1742StrongTransOfHom (F := S2847A6.F) (S2882A6Aut (f.as : Iut.SignGroup))) ≫
      S1742HomOfStrongTrans (F := S2847A6.F)
        (S1742StrongTransOfHom (F := S2847A6.F) (S2882A6Aut (g.as : Iut.SignGroup)))
  rw [S1742HomOfStrongTrans_strongTransOfHom, S1742HomOfStrongTrans_strongTransOfHom,
    S1742HomOfStrongTrans_strongTransOfHom]
  exact S2980Aut_comp_as f g

/-- **The sign-action pseudofunctor on the A6 curve.**  Its object is the
representable stack of `S2844X` and its generator is the actual elliptic
involution.  All 2-cell coherences are subsingleton. -/
noncomputable def S2980D : Pseudofunctor Iut.SignActionIndex
    (Iut.EtaleStackPseudofunctor S2847A6.F) where
  obj := fun _ => S2980Q
  map := fun {a b} f => S2980SigMap f
  map₂ := fun {a b} {f g} η =>
    eqToHom (congrArg S2980SigMap (LocallyDiscrete.eq_of_hom η))
  map₂_id := fun f => (S2980StrongTransSubsingleton _ _).elim _ _
  map₂_comp := fun η θ => (S2980StrongTransSubsingleton _ _).elim _ _
  mapId := fun a => S2980MapId a
  mapComp := fun f g => S2980MapComp f g
  map₂_whisker_left := fun f g h η => (S2980StrongTransSubsingleton _ _).elim _ _
  map₂_whisker_right := fun η h => (S2980StrongTransSubsingleton _ _).elim _ _
  map₂_associator := fun f g h => (S2980StrongTransSubsingleton _ _).elim _ _
  map₂_left_unitor := fun f => (S2980StrongTransSubsingleton _ _).elim _ _
  map₂_right_unitor := fun f => (S2980StrongTransSubsingleton _ _).elim _ _

/-- The adjoint equivalence from the diagram object to the A6 fiber, taken to be
the identity. -/
noncomputable def S2980AtBase :
    Bicategory.Equivalence (S2980D.obj Iut.signActionObject)
      S2855HyperbolicOrbicurve.stack.fiber where
  hom := 𝟙 S2980Q
  inv := 𝟙 S2980Q
  unit := (ρ_ (𝟙 S2980Q)).symm
  counit := ρ_ (𝟙 S2980Q)
  left_triangle := by
    apply Iso.ext
    exact (S2980StrongTransSubsingleton _ _).elim _ _

/-- The generator of the diagram is the elliptic involution. -/
theorem S2980D_map_generator :
    S2980D.map Iut.signActionGenerator = S2857StackAuto alphaOverS2844 := by
  change S1742StrongTransOfHom (F := S2847A6.F)
      (S2882A6Aut (Iut.signActionGenerator.as : Iut.SignGroup)) =
    S1742StrongTransOfHom (F := S2847A6.F) alphaOverS2844
  rw [S2980SignGenAs, S2882A6Aut_gen]

/-- A general unitor: composing the identity on both sides with a
strong transformation gives back that strong transformation. -/
noncomputable def S2980CompIdLeft (f : S2980Q ⟶ S2980Q) :
    (𝟙 S2980Q ≫ f) ≫ 𝟙 S2980Q ≅ f :=
  (ρ_ (𝟙 S2980Q ≫ f)).trans (λ_ f)

/-- The generator identification: after `atBase`, the diagram generator is the
actual elliptic involution. -/
noncomputable def S2980GeneratorIdentification :
    (S2980AtBase.inv ≫ S2980D.map Iut.signActionGenerator) ≫ S2980AtBase.hom ≅
      S2857StackAuto alphaOverS2844 := by
  rw [S2980D_map_generator]
  exact S2980CompIdLeft (S2857StackAuto alphaOverS2844)

/-! ## 4. The consumer sign action is actual -/

/-- The sign action of `S2869`, filled with the actual diagram, base equivalence
and generator identification. -/
noncomputable def S2980A :
    Iut.OrbicurveSignAction S2855HyperbolicOrbicurve :=
  S2869SignAction S2980D S2980AtBase S2980GeneratorIdentification

/-! ## 5. The first blocked input of W -/

/-- **The pointwise quotient is not a stack** (hence `hQ` is refuted, not
merely missing).  Re-export of the empty-base obstruction of S2975b/S2993. -/
theorem S2980NotHQ :
    ¬ S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F) :=
  S2993_not_isStack

/-- The pointwise quotient is not even a prestack. -/
theorem S2980NotPrestack :
    ¬ S2882A6Q.IsPrestack (Iut.SchemeOverField.etaleTopology S2847A6.F) :=
  S2993_not_isPrestack

/-- Any hypothetical quotient-witness datum for `S2882A6Q` is vacuous: its
`hQ` argument is refuted. -/
theorem S2980W_vacuous
    (A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve)
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F))
    (W : S2870QuotientWitnessData S2882A6Q hQ A) : False :=
  S2980NotHQ hQ

#check S2980D
#check S2980AtBase
#check S2980GeneratorIdentification
#check S2980A
#check S2869SignAction S2980D S2980AtBase S2980GeneratorIdentification
#check S2980NotHQ
#check S2980W_vacuous

#print axioms S2980FiberEq
#print axioms S2980D
#print axioms S2980AtBase
#print axioms S2980D_map_generator
#print axioms S2980GeneratorIdentification
#print axioms S2980A
#print axioms S2980NotHQ
#print axioms S2980W_vacuous

end LeanFormal.IUT.XiFPaper.S2980QuotientStackActual
end
