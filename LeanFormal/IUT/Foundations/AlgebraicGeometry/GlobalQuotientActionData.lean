import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalActionCocone
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Tactic

/-!
# Action data on global quotient chart presentations

This file records the action of a finite group on the chart presentation and
the induced action on the glued quotient candidate. It is data only; no
universal property or provider is asserted.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option maxRecDepth 10000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartPresentation
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalActionCocone
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]

/-- An action of G on a chart presentation: a permutation of charts, chart
automorphisms over the base, and the induced action on the glued quotient. -/
structure GlobalQuotientActionData
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) (G : Type u) [Group G] where
  presentation : GlobalQuotientChartPresentation (Spec (CommRingCat.of R))
  chartIso : X.carrier ≅ presentation.glued
  overTriangle : chartIso.hom ≫ FiniteEtaleCover.structureMap presentation.cover =
    FiniteEtaleCover.structureMap X
  chartAction : G →* Equiv.Perm presentation.J
  chartHom : ∀ (g : G) (i : presentation.J),
    presentation.U i ⟶ presentation.U (chartAction g i)
  chartHom_one : ∀ i, chartHom 1 i = 𝟙 _
  chartHom_mul : ∀ (g h : G) (i : presentation.J),
    chartHom (g * h) i = chartHom g i ≫ chartHom h (chartAction g i)
  chartHom_over : ∀ (g : G) (i : presentation.J),
    chartHom g i ≫ presentation.q (chartAction g i) = presentation.q i
  overlapCompat : ∀ (g : G) (i j : presentation.J),
    pullback.fst (presentation.chartι i) (presentation.chartι j) ≫ chartHom g i =
      pullback.snd (presentation.chartι i) (presentation.chartι j) ≫ chartHom g j
  coverAction : G →* CategoryTheory.Aut X
  coverAction_chartIso : ∀ g : G,
    (coverAction g).hom ≫ chartIso.hom = chartIso.hom

namespace GlobalQuotientActionData

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  (A : GlobalQuotientActionData (R := R) X G)

/-- The underlying chart presentation. -/
abbrev presentation : GlobalQuotientChartPresentation (Spec (CommRingCat.of R)) := A.presentation

/-- The glued quotient scheme. -/
abbrev glued : Scheme.{u} := A.presentation.glued

/-- The quotient cover. -/
noncomputable abbrev quotientCover : FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  A.presentation.cover

/-- The projection from X to the quotient candidate. -/
noncomputable def projection : X ⟶ A.quotientCover :=
  AffineLocalQuotientGluingConstruct.finiteEtaleCoverHomMk (X := X) (Y := A.quotientCover)
    A.chartIso.hom A.overTriangle

/-- The chart action as a permutation of charts. -/
abbrev chartPerm (g : G) : Equiv.Perm A.presentation.J := A.chartAction g

/-- The chart action at the identity is the identity chart hom. -/
theorem chartHom_one_apply (i : A.presentation.J) : A.chartHom 1 i = 𝟙 _ :=
  A.chartHom_one i

/-- The chart action is multiplicative. -/
theorem chartHom_mul_apply (g h : G) (i : A.presentation.J) :
    A.chartHom (g * h) i = A.chartHom g i ≫ A.chartHom h (A.chartPerm g i) :=
  A.chartHom_mul g h i

/-- The chart action is over the base. -/
theorem chartHom_over_apply (g : G) (i : A.presentation.J) :
    A.chartHom g i ≫ A.presentation.q (A.chartPerm g i) = A.presentation.q i :=
  A.chartHom_over g i

/-- The chart action is compatible with the overlap pullbacks. -/
theorem overlapCompat_apply (g : G) (i j : A.presentation.J) :
    pullback.fst (A.presentation.chartι i) (A.presentation.chartι j) ≫ A.chartHom g i =
      pullback.snd (A.presentation.chartι i) (A.presentation.chartι j) ≫ A.chartHom g j :=
  A.overlapCompat g i j

/-- The cover action commutes with the chart identification. -/
theorem coverAction_chartIso_apply (g : G) :
    (A.coverAction g).hom ≫ A.chartIso.hom = A.chartIso.hom :=
  A.coverAction_chartIso g

/-- The projection is invariant under the cover action. -/
theorem projection_invariant (g : G) :
    (A.coverAction g).hom ≫ A.projection = A.projection := by
  apply finiteEtaleCoverHom_ext (R := R)
  change (A.coverAction g).hom.hom.left ≫ A.chartIso.hom =
    A.chartIso.hom
  exact congrArg (fun f : X.carrier ⟶ A.glued => f) (A.coverAction_chartIso g)

/-- The action functor associated to the cover action. -/
def actionFunctor : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R)) where
  obj _ := X
  map g := (A.coverAction g).hom
  map_id := by
    intro j
    change (A.coverAction 1).hom = 𝟙 X
    rw [map_one]
    rfl
  map_comp := by
    intro f g
    change (A.coverAction (f ≫ g)).hom = (A.coverAction f).hom ≫ (A.coverAction g).hom
    rw [map_mul]
    rfl

/-- The quotient cocone attached to the action data. -/
def cocone : Cocone A.actionFunctor where
  pt := A.quotientCover
  ι :=
    { app := fun _ => A.projection
      naturality := by
        intro j j' f
        change A.projection = _
        simpa [actionFunctor, projection] using (A.projection_invariant f).symm }

/-- The quotient cocone is a cocone over the action functor. -/
theorem cocone_pt : A.cocone.pt = A.quotientCover := rfl

/-- The cocone component at the unique object is the projection. -/
theorem cocone_ι (j : SingleObj G) : A.cocone.ι.app j = A.projection := rfl

/-- The action data packaged as global action data. -/
noncomputable def toGlobalActionData : GlobalActionData (R := R) X G :=
  { D := A.presentation.toGlobalGluedQuotientData
    chartIso := A.chartIso
    overTriangle := A.overTriangle
    action := A.coverAction
    projection_invariant := A.projection_invariant }

/-- The packaged global action data has the same quotient cover. -/
theorem toGlobalActionData_cover :
    A.toGlobalActionData.D.cover = A.quotientCover := rfl

/-- The packaged global action data has the same projection. -/
theorem toGlobalActionData_projection :
    A.toGlobalActionData.projection = A.projection := rfl

/-- The quotient cocone of the packaged data agrees with the action-data cocone. -/
theorem toGlobalActionData_cocone :
    A.toGlobalActionData.cocone = A.cocone := rfl

end GlobalQuotientActionData

/-- A chart action is trivial if all chart homs are identities. -/
def GlobalQuotientActionData.IsTrivial
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    (A : GlobalQuotientActionData (R := R) X G) : Prop :=
  ∀ (g : G) (i : A.presentation.J), A.chartHom g i = 𝟙 _

/-- The trivial chart action has identity chart homs. -/
theorem GlobalQuotientActionData.isTrivial_chartHom
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
    (A : GlobalQuotientActionData (R := R) X G)
    (h : A.IsTrivial) (g : G) (i : A.presentation.J) :
    A.chartHom g i = 𝟙 _ :=
  h g i


namespace GlobalQuotientActionData

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  (A : GlobalQuotientActionData (R := R) X G)

/-- The quotient action on the glued scheme, induced by the chart action. -/
noncomputable def gluedAction (g : G) : A.glued ⟶ A.glued :=
  A.presentation.P.descOfCompatible A.glued
    (fun i => A.chartHom g i ≫ A.presentation.chartι (A.chartPerm g i))
    (by
      intro i j
      rw [← Category.assoc, A.overlapCompat g i j, Category.assoc]
      congr 1
      exact A.presentation.P.gluedMapOfCompatible_ι A.presentation.hq (A.chartPerm g j))

/-- The glued action restricts to the chart action. -/
theorem gluedAction_fac (g : G) (i : A.presentation.J) :
    A.presentation.chartι i ≫ A.gluedAction g =
      A.chartHom g i ≫ A.presentation.chartι (A.chartPerm g i) :=
  A.presentation.P.descOfCompatible_ι A.glued
    (fun i => A.chartHom g i ≫ A.presentation.chartι (A.chartPerm g i))
    (by
      intro i j
      rw [← Category.assoc, A.overlapCompat g i j, Category.assoc]
      congr 1
      exact A.presentation.P.gluedMapOfCompatible_ι A.presentation.hq (A.chartPerm g j)) i

/-- The glued action at the identity is the identity. -/
theorem gluedAction_one : A.gluedAction 1 = 𝟙 A.glued := by
  apply A.presentation.desc_uniq
    (A.presentation.P.q) A.presentation.P.hq
  · intro i
    rw [gluedAction_fac, A.chartHom_one]
    simp
  · intro i
    rw [gluedAction_fac, A.chartHom_one]
    simp

/-- The glued action is multiplicative. -/
theorem gluedAction_mul (g h : G) :
    A.gluedAction (g * h) = A.gluedAction g ≫ A.gluedAction h := by
  apply A.presentation.desc_uniq
    A.presentation.P.q A.presentation.P.hq
  · intro i
    rw [gluedAction_fac, A.chartHom_mul]
    simp only [Category.assoc]
    congr 1
    rw [gluedAction_fac]
  · intro i
    rw [gluedAction_fac, A.chartHom_mul]
    simp only [Category.assoc]
    congr 1
    rw [gluedAction_fac]

/-- The glued action lies over the base. -/
theorem gluedAction_over (g : G) :
    A.gluedAction g ≫ A.presentation.gluedMap = A.presentation.gluedMap := by
  apply A.presentation.desc_uniq A.presentation.P.q A.presentation.P.hq
  · intro i
    rw [Category.assoc, gluedAction_fac, A.chartHom_over]
    exact A.presentation.P.gluedMapOfCompatible_ι A.presentation.hq i
  · intro i
    rw [gluedAction_fac, A.chartHom_over]
    exact A.presentation.P.gluedMapOfCompatible_ι A.presentation.hq i

/-- The glued action gives a group action on the glued scheme. -/
noncomputable def gluedMulAction : MulAction G A.glued where
  smul g x := A.gluedAction g x
  one_smul x := by rw [gluedAction_one]; rfl
  mul_smul g h x := by rw [gluedAction_mul]; rfl

/-- The glued action is compatible with the chart cover map. -/
theorem gluedAction_chartMap (g : G) (i : A.presentation.J) :
    A.presentation.chartMap i ≫ A.gluedAction g =
      A.chartHom g i ≫ A.presentation.chartMap (A.chartPerm g i) := by
  change A.presentation.chartι i ≫ A.gluedAction g = _
  exact A.gluedAction_fac g i

/-- The chart action permutes the charts covering the glued quotient. -/
theorem chartPerm_bijective (g : G) :
    Function.Bijective (A.chartPerm g : A.presentation.J → A.presentation.J) :=
  (A.chartPerm g).bijective

end GlobalQuotientActionData

namespace GlobalQuotientActionData

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]

/-- Two action data are chart-compatible if their chart homs agree after
transporting by the chart permutations. -/
def ChartCompatible
    (A B : GlobalQuotientActionData (R := R) X G) : Prop :=
  A.presentation = B.presentation ∧
    ∀ (g : G) (i : A.presentation.J),
      cast (by rw [‹A.presentation = B.presentation›]) (A.chartHom g i) =
        B.chartHom g i

/-- Chart compatibility is reflexive. -/
theorem chartCompatible_refl (A : GlobalQuotientActionData (R := R) X G) :
    A.ChartCompatible A := by
  refine ⟨rfl, ?_⟩
  intro g i
  rfl

/-- Chart compatibility preserves the induced cocone. -/
theorem chartCompatible_cocone {A B : GlobalQuotientActionData (R := R) X G}
    (h : A.ChartCompatible B) : A.cocone = B.cocone := by
  cases h with
  | intro hp hh =>
    cases hp
    rfl

end GlobalQuotientActionData


namespace GlobalQuotientActionData

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  (A : GlobalQuotientActionData (R := R) X G)

/-- The chart action permutation at the identity is the identity permutation. -/
theorem chartPerm_one : A.chartPerm 1 = 1 := by
  ext i
  exact congrArg (fun e : Equiv.Perm A.presentation.J => e i) (map_one A.chartAction)

/-- The chart action permutation is multiplicative. -/
theorem chartPerm_mul (g h : G) :
    A.chartPerm (g * h) = A.chartPerm g * A.chartPerm h := by
  ext i
  exact congrArg (fun e : Equiv.Perm A.presentation.J => e i) (map_mul A.chartAction g h)

/-- The chart action inverse permutes back. -/
theorem chartPerm_symm_apply (g : G) (i : A.presentation.J) :
    A.chartPerm g ((A.chartPerm g).symm i) = i :=
  (A.chartPerm g).apply_symm_apply i

/-- The chart action at the inverse is the inverse permutation. -/
theorem chartPerm_inv (g : G) :
    A.chartPerm g⁻¹ = (A.chartPerm g)⁻¹ := by
  rw [← map_inv]
  rfl

/-- The chart homs at the inverse recover the original chart after permutation. -/
theorem chartHom_inv_apply (g : G) (i : A.presentation.J) :
    A.chartHom g⁻¹ (A.chartPerm g i) ≫ A.chartHom g i = 𝟙 _ := by
  rw [← A.chartHom_mul g⁻¹ g i, inv_mul_cancel, A.chartHom_one]

/-- The chart homs preserve the chart-cover maps. -/
theorem chartMap_action (g : G) (i : A.presentation.J) :
    A.presentation.chartMap i ≫ A.gluedAction g =
      A.chartHom g i ≫ A.presentation.chartMap (A.chartPerm g i) :=
  A.gluedAction_chartMap g i

/-- The glued action is a group action in the categorical sense. -/
theorem gluedAction_comp (g h : G) :
    A.gluedAction (g * h) = A.gluedAction g ≫ A.gluedAction h :=
  A.gluedAction_mul g h

/-- The glued action preserves the glued quotient structure map. -/
theorem gluedAction_structureMap (g : G) :
    A.gluedAction g ≫ FiniteEtaleCover.structureMap A.quotientCover =
      FiniteEtaleCover.structureMap A.quotientCover :=
  A.gluedAction_over g

/-- The cover action is compatible with the projection to the quotient. -/
theorem coverAction_projection (g : G) :
    (A.coverAction g).hom ≫ A.projection = A.projection :=
  A.projection_invariant g

/-- The action data induces a cocone map to the quotient cover. -/
theorem cocone_fac (g : G) :
    (A.actionFunctor.map g) ≫ A.cocone.ι.app (SingleObj.star G) =
      A.cocone.ι.app (SingleObj.star G) := by
  simpa [actionFunctor, cocone] using A.projection_invariant g

end GlobalQuotientActionData


namespace GlobalQuotientActionData

variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))} {G : Type u} [Group G]
  (A : GlobalQuotientActionData (R := R) X G)

/-- The chart action and the glued action agree on the chart cover. -/
theorem chart_hom_glued (g : G) (i : A.presentation.J) :
    A.chartHom g i ≫ A.presentation.chartι (A.chartPerm g i) =
      A.presentation.chartι i ≫ A.gluedAction g :=
  (A.gluedAction_fac g i).symm

/-- The glued action preserves the image of every chart. -/
theorem gluedAction_image_chart (g : G) (i : A.presentation.J) :
    Set.range (A.presentation.chartι i ≫ A.gluedAction g) =
      Set.range (A.presentation.chartι (A.chartPerm g i)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨A.chartHom g i y, (A.gluedAction_fac g i).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(A.chartHom g⁻¹ (A.chartPerm g i)) y, by
      rw [← Category.assoc, A.gluedAction_fac, ← Category.assoc,
        A.chartHom_inv_apply]
      simp⟩

/-- The quotient cover map of the action data is equivariant when the cover
action is the chart action. -/
theorem projection_equivariant (g : G) :
    (A.coverAction g).hom ≫ A.projection = A.projection :=
  A.projection_invariant g

end GlobalQuotientActionData

end LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
