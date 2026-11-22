import tmp.sheaf.xif.paper.S2158QStackActual
import tmp.sheaf.xif.paper.S2134D9DescentActual
import Mathlib.AlgebraicGeometry.Limits

/-!
# S2134: the prestack and descent status of the actual pointwise colimit Q

The S2152 pointwise functorial colimit `Q = S2152Q` is an actual category-valued
pseudofunctor on the etale site of `SchemeOverField F'`.  S2149/S2158 decompose
its stack condition exactly into

  `Q.IsStack J  <->  Q.IsPrestack J  /\  S2149EffectiveDescent l Q`.

This file settles the following.

## 1. `Q.IsPrestack` is *false* for the etale topology

The etale topology on schemes has the empty sieve as a covering sieve of the
empty scheme (`AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology`), and this
propagates to the slice site `J.over S` and to the double slice.  The fibre of
`Q` at the empty test object is the action groupoid of the sign group on the
one-point type `(empty scheme -> affine model)`; it therefore has two
endomorphisms of every object, `1` and the nontrivial sign element.  The empty
sieve forces the value of every hom presheaf at the identity slice object to be
a subsingleton, which it is not.  Hence `Q` is not a prestack, and consequently
`S2152QIsStack` is false.  `S2134QNotPrestack` and `S2134QNotStack` below are
unconditional.

This is the exact first obstruction, and it is *purely* the empty test object:
the sign action itself is defined by the actual elliptic involution, and the
nontriviality used is `S1963SignGroup_generator_ne`.

## 2. What is nevertheless actual: effective descent data

Independent of the prestack failure, effective descent for `Q` is a genuine
construction on every cover whose generated sieve is maximal (e.g. the identity
cover, or any cover containing a split epimorphism).  There, every descent datum
for `Q` has an actual amalgamation, produced by `S2134D9DescentActual`
(`hasEffectiveDescent_iff_amalgam`).  This is recorded as
`S2134QAmalgam_top`, `S2134QEffectiveDescent_top`,
`S2134QEffectiveDescentPresieve_of_generate_top` and `S2134QAmalgam_idFamily`.

## 3. The exact remaining statement

Since `Q.IsStack` is refuted, the mathematically meaningful remaining target is
the same descent statement with the degenerate empty test object excluded; it is
recorded, unproved, as `S2134QPrestackOnNonempty`.  Nothing in this file asserts
it, and no `IsStack` instance is produced.

No `sorry`, no `admit`, no new axiom, no `True`/`PUnit`/`ULift` carrier: every
object used below (`Q`, the sign group, the empty scheme, the slice sites) is an
actual object of the tree or of Mathlib.
-/

noncomputable section
open CategoryTheory Opposite

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2134QIsPrestackDescentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2149StackFiberDataActual
open LeanFormal.IUT.XiFPaper.S2158QStackActual
open LeanFormal.IUT.XiFPaper.S2143StackQuotientWitnessActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S1963SignActionAssemblyActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open AlgebraicGeometry

/-! ## 1. The empty test object and its slice -/

/-- The empty test object: the initial scheme of `Scheme`, over `Spec F'`. -/
noncomputable abbrev S2134EmptyOver : Iut.SchemeOverField S1726K :=
  Over.mk (Scheme.emptyTo (Spec (CommRingCat.of S1726K)))

/-- The underlying scheme of the empty test object is the empty scheme. -/
theorem S2134EmptyOver_left : S2134EmptyOver.left = (∅ : Scheme) := rfl

instance S2134EmptyOver_instIsEmpty : IsEmpty S2134EmptyOver.left := by
  rw [S2134EmptyOver_left]
  infer_instance

/-- All points of the affine model over an empty test object coincide, in the
over-category of schemes over `Spec F'`. -/
theorem S2134EmptyPointSubsingleton (T : Over S2134EmptyOver)
    (hT : IsEmpty T.left.left) :
    Subsingleton (T.left ⟶ S1726AffineOver) :=
  ⟨fun a b => Over.OverMorphism.ext
    ((isInitialOfIsEmpty (X := T.left.left)).hom_ext a.left b.left)⟩

/-- The canonical object of `Q` at the empty test object: the unique point of the
affine model, as an object of the pointwise action groupoid. -/
noncomputable def S2134EmptyPoint :
    S2134EmptyOver ⟶ S1726AffineOver :=
  Over.homMk (Scheme.emptyTo S1726AffineScheme) (Subsingleton.elim _ _)

/-- The same point, as an object of the action groupoid. -/
noncomputable def S2134EmptyObj :
    S2152Q.obj (LocallyDiscrete.mk (Opposite.op S2134EmptyOver)) :=
  show ActionCategory SignGroup (S2134EmptyOver ⟶ S1726AffineOver) from
    (S2134EmptyPoint :)

/-! ## 2. The bottom sieve is covering on the empty slice -/

/-- The bottom sieve of an over-site is covering whenever the bottom sieve of the
base topology at the source is covering. -/
theorem S2134bot_mem_over {C : Type*} [Category C] {J : GrothendieckTopology C}
    {X : C} (Y : Over X) (h : (⊥ : Sieve Y.left) ∈ J Y.left) :
    (⊥ : Sieve Y) ∈ J.over X Y := by
  rw [GrothendieckTopology.mem_over_iff,
    show Sieve.overEquiv Y (⊥ : Sieve Y) = ⊥ from OrderIso.map_bot (Sieve.overEquiv Y)]
  exact h

/-- The empty sieve is a covering sieve of the identity slice object of the
empty test object, for the etale topology of `SchemeOverField F'`. -/
theorem S2134Empty_bot_mem :
    (⊥ : Sieve (Over.mk (𝟙 S2134EmptyOver))) ∈
      (Iut.SchemeOverField.etaleTopology S1726K).over S2134EmptyOver
        (Over.mk (𝟙 S2134EmptyOver)) := by
  refine S2134bot_mem_over (Over.mk (𝟙 S2134EmptyOver)) ?_
  show (⊥ : Sieve S2134EmptyOver) ∈
    GrothendieckTopology.over AlgebraicGeometry.Scheme.etaleTopology
      (Spec (CommRingCat.of S1726K)) S2134EmptyOver
  refine S2134bot_mem_over S2134EmptyOver ?_
  exact AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology
    (P := @AlgebraicGeometry.Etale) S2134EmptyOver.left

/-! ## 3. The value of the hom presheaf is not a subsingleton -/

/-- **The value of the hom presheaf of `Q` at any empty slice object is not a
subsingleton.**  The action groupoid at an empty test scheme has the identity and
the nontrivial sign automorphism of every object, because every point of the
affine model over an empty scheme is the same point. -/
theorem S2134EmptyValue_not_subsingleton
    (T : Over S2134EmptyOver) (hT : IsEmpty T.left.left) :
    ¬ Subsingleton
      ((S2152Q.presheafHom S2134EmptyObj S2134EmptyObj).obj (Opposite.op T)) := by
  intro h
  let P : S2152Q.obj (LocallyDiscrete.mk (Opposite.op T.left)) :=
    (S2152Q.map (T.unop.hom.op.toLoc)).toFunctor.obj S2134EmptyObj
  have hval :
      (S2152Q.presheafHom S2134EmptyObj S2134EmptyObj).obj (Opposite.op T) =
        (P ⟶ P) := rfl
  rw [hval] at h
  haveI := h
  obtain ⟨φ, hφ⟩ := S1971PointwiseQuotient_fixed_nontrivial_aut
    (U := LocallyDiscrete.mk (Opposite.op T.left))
    (P := P) (S2134EmptyPointSubsingleton T hT).elim
  exact hφ (Subsingleton.elim φ _)

/-! ## 4. `Q` is not a prestack and not a stack -/

/-- **The actual pointwise colimit `Q` is not a prestack** for the etale topology:
the empty covering sieve of the empty test object forces the hom presheaf value
at the identity slice object to be a subsingleton. -/
theorem S2134QNotPrestack :
    ¬ S2152Q.IsPrestack (Iut.SchemeOverField.etaleTopology S1726K) := by
  intro hpre
  have hsheaf := hpre.isSheaf (S := S2134EmptyOver) S2134EmptyObj S2134EmptyObj
  have hsheaf' :
      Presieve.IsSheaf
        ((Iut.SchemeOverField.etaleTopology S1726K).over S2134EmptyOver)
        (S2152Q.presheafHom S2134EmptyObj S2134EmptyObj) :=
    (isSheaf_iff_isSheaf_of_type
      (J := (Iut.SchemeOverField.etaleTopology S1726K).over S2134EmptyOver)
      (S2152Q.presheafHom S2134EmptyObj S2134EmptyObj)).mp hsheaf
  have hbot := S2134Empty_bot_mem
  have hsf := hsheaf' (S := Over.mk (𝟙 S2134EmptyOver))
    (⊥ : Sieve (Over.mk (𝟙 S2134EmptyOver))) hbot
  have hsub : Subsingleton
      ((S2152Q.presheafHom S2134EmptyObj S2134EmptyObj).obj
        (Opposite.op (Over.mk (𝟙 S2134EmptyOver)))) := by
    refine ⟨fun a b => ?_⟩
    let x : Presieve.FamilyOfElements
        (S2152Q.presheafHom S2134EmptyObj S2134EmptyObj)
        (((⊥ : Sieve (Over.mk (𝟙 S2134EmptyOver)))) : Presieve _) :=
      fun _ _ hf => (hf : (⊥ : Presieve _) _).elim
    have hc : x.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ h
      exact (h₁ : (⊥ : Presieve _) f₁).elim
    obtain ⟨t, -, huniq⟩ := hsf x hc
    rw [huniq a (fun _ _ hf => (hf : (⊥ : Presieve _) _).elim),
      huniq b (fun _ _ hf => (hf : (⊥ : Presieve _) _).elim)]
  exact S2134EmptyValue_not_subsingleton (Over.mk (𝟙 S2134EmptyOver))
    (by rw [show (Over.mk (𝟙 S2134EmptyOver) : Over S2134EmptyOver).left =
        S2134EmptyOver from rfl]; infer_instance) hsub

/-- **The target `S2152QIsStack` is false**: the stack condition contains the
prestack condition, which fails on the empty test object. -/
theorem S2134QNotStack : ¬ S2152QIsStack :=
  fun h => S2134QNotPrestack h.toIsPrestack

/-- The required descent API of S2149 is likewise refuted. -/
theorem S2134QNotRequiredDescentAPI (l : PrimeGeFive) :
    ¬ S2149RequiredDescentAPI l S2152Q :=
  fun h => S2134QNotPrestack h.1

/-- The exact decomposition of the stack condition still holds as an equivalence
of props (the S2149 splitting); its left-hand side is now known to be false. -/
theorem S2134QIsStack_iff_descent (l : PrimeGeFive) :
    S2152QIsStack ↔
      S2152Q.IsPrestack (Iut.SchemeOverField.etaleTopology S1726K) ∧
        S2149EffectiveDescent l S2152Q :=
  S2152QIsStack_iff_descent l

/-- The decomposed form of the refutation: even though the S2149 splitting is
exact, no pair of a prestack structure and effective descent for `Q` exists. -/
theorem S2134QNotPrestackAndDescent (l : PrimeGeFive) :
    ¬ (S2152Q.IsPrestack (Iut.SchemeOverField.etaleTopology S1726K) ∧
        S2149EffectiveDescent l S2152Q) :=
  fun h => S2134QNotPrestack h.1

/-! ## 5. Actual effective descent data on the covers with maximal sieve -/

/-- **Effective descent for the top presieve of `Q`**: every descent datum for
`Q` along the maximal presieve has an actual amalgamation. -/
theorem S2134QEffectiveDescent_top (S : Iut.SchemeOverField S1726K) :
    HasEffectiveDescentPresieve S2152Q (⊤ : Presieve S) :=
  hasEffectiveDescentPresieve_top S2152Q

/-- Effective descent for every presieve of `Q` whose generated sieve is maximal,
i.e. for every cover refined by the identity, in particular every cover containing
a split epimorphism. -/
theorem S2134QEffectiveDescentPresieve_of_generate_top
    (S : Iut.SchemeOverField S1726K) (R : Presieve S)
    (hR : Sieve.generate R = ⊤) :
    HasEffectiveDescentPresieve S2152Q R :=
  hasEffectiveDescentPresieve_of_generate_top S2152Q R hR

/-- The same statement for a cover containing a split epimorphism. -/
theorem S2134QEffectiveDescent_of_contains_isSplitEpi
    {S : Iut.SchemeOverField S1726K} (R : Presieve S)
    {Y : Iut.SchemeOverField S1726K} (f : Y ⟶ S) [IsSplitEpi f] (hf : R f) :
    HasEffectiveDescentPresieve S2152Q R :=
  hasEffectiveDescentPresieve_of_contains_isSplitEpi S2152Q R f hf

/-- **The amalgamation form**: for the maximal presieve, every descent datum for
`Q` is isomorphic to the descent data of an actual object of the fibre of `Q` at
the base. -/
theorem S2134QAmalgam_top (S : Iut.SchemeOverField S1726K)
    (D : S2152Q.DescentData (fun g : (⊤ : Presieve S).category => g.obj.hom)) :
    Nonempty (Amalgam S2152Q (fun g : (⊤ : Presieve S).category => g.obj.hom) D) :=
  (hasEffectiveDescent_iff_amalgam S2152Q
    (fun g : (⊤ : Presieve S).category => g.obj.hom)).mp
    (S2134QEffectiveDescent_top S) D

/-- **The amalgamation form for the identity cover**: the actual object glued from
a descent datum on the identity cover. -/
theorem S2134QAmalgam_idFamily (S : Iut.SchemeOverField S1726K)
    (D : S2152Q.DescentData (fun _ : Unit => (𝟙 S : S ⟶ S))) :
    Nonempty (Amalgam S2152Q (fun _ : Unit => (𝟙 S : S ⟶ S)) D) :=
  (hasEffectiveDescent_iff_amalgam S2152Q
    (fun _ : Unit => (𝟙 S : S ⟶ S))).mp (hasEffectiveDescent_idFamily S2152Q) D

/-! ## 6. The exact remaining statement -/

/-- The remaining mathematical target: the prestack condition of `Q` at the
nondegenerate test objects, i.e. with the empty test scheme excluded.  It is the
only part of `Q.IsPrestack` that is not refuted by the empty sieve; it is *not*
proved here and no inhabitant is asserted. -/
def S2134QPrestackOnNonempty : Prop :=
  ∀ (S : Iut.SchemeOverField S1726K) [Nonempty S.left],
    ∀ M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)),
      Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S)
        (S2152Q.presheafHom M N)

/-! ## 7. Axiom footprint -/

#print axioms S2134EmptyOver_left
#print axioms S2134EmptyPointSubsingleton
#print axioms S2134bot_mem_over
#print axioms S2134Empty_bot_mem
#print axioms S2134EmptyValue_not_subsingleton
#print axioms S2134QNotPrestack
#print axioms S2134QNotStack
#print axioms S2134QNotRequiredDescentAPI
#print axioms S2134QIsStack_iff_descent
#print axioms S2134QNotPrestackAndDescent
#print axioms S2134QEffectiveDescent_top
#print axioms S2134QEffectiveDescentPresieve_of_generate_top
#print axioms S2134QEffectiveDescent_of_contains_isSplitEpi
#print axioms S2134QAmalgam_top
#print axioms S2134QAmalgam_idFamily

end LeanFormal.IUT.XiFPaper.S2134QIsPrestackDescentActual
