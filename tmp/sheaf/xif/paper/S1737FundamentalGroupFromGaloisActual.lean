/-
# S1737: actual profinite fundamental groups from Mathlib Galois theory

## Question

The D6 source clause needs the datum

  Iut.OrbicurveFundamentalGroupData S1726Orbicurve
    (Iut.AbsoluteGaloisProfinite S1726K).

Its first ingredient is an `OrbicurveEtaleFundamentalGroup`, and the
abstract group-theoretic input is the Galois-category theorem for finite
actions of the absolute Galois group.

This file separates three statements that are often conflated:

* the category `Action FintypeCat G` of ALL finite actions of a profinite
  group `G`;
* Mathlib's full subcategory `ContAction FintypeCat G` of finite actions
  whose action map is continuous;
* the actual orbicurve cover category `OrbicurveFiniteEtaleCover X`, which is
  not either of the two action categories.

## Result

1. For a profinite group `G`, the continuous finite `G`-sets form a Galois
   category and `G` itself is its fundamental group:

     PreGaloisCategory.IsFundamentalGroup (Iut.continuousActionFiber G) G.

   This is the actual profinite fundamental group, not a replacement by
   `Aut`.  It is packaged as an `Iut.EtaleFundamentalGroup` in
   `S1737ContinuousEtaleFundamentalGroup`.

2. The literal target with the FULL action category,

     PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat G) G,

   is not available for a general profinite `G`.  The class
   `IsFundamentalGroup` has a field `continuous_smul`; for
   `F = Action.forget FintypeCat G` this requires every finite `G`-action to
   be continuous.  That condition is not automatic for an infinite profinite
   group: a finite-index subgroup need not be open.  We prove the exact
   conditional theorem and the equivalence

     IsFundamentalGroup (Action.forget FintypeCat G) G
       ↔ S1737AllFiniteActionsContinuous G
       ↔ S1737EveryFiniteIndexSubgroupOpen G.

   Thus `every finite-index subgroup of G is open` is the precise
   group-theoretic missing hypothesis of the literal statement.  It is
   discharged for finite `G`
   (`S1737ActionForget_isFundamentalGroup_of_finite`), but Mathlib supplies
   neither this condition nor its negation for a general
   `AbsoluteGaloisProfinite F`.  For an infinite non-strongly-complete
   profinite group the condition fails, so the literal statement is not
   merely unproved but false in that case.

3. `OrbicurveEtaleFundamentalGroup` is a different structure: its
   `coverCategory` is `Category.{0} (OrbicurveFiniteEtaleCover X)`, not
   `Action FintypeCat G`.  The eleven requested fields are recorded with
   their exact types in `S1737OrbicurveFields`.  For the S1726 representable
   orbicurve, the `baseScheme` and `basePoint` fields are actually
   constructed (`S1737S1726BaseFieldsActual`): the stack fiber is the
   representable pseudofunctor of `S1726AffineOver`, and the identity strong
   transformation is a genuine point of it.  The remaining fields are not
   constructed.  The exact first missing field is a small
   `Category.{0}` on the Type 1 cover type (S1728); the categorical fields
   depend on it.  The two geometric fields `geometricFiberFintype` and
   `fiberIdentification` depend only on the base fields, but still require
   the missing finiteness and identification of the literal geometric
   fibers.

## Honest boundary

No `sorry`, `admit`, new axiom, `Shrink`, `ULift`, `PUnit`, fake group,
fake action, or fake category is introduced.  The conditional theorem is a
real proof; the missing hypothesis is named and, in the finite case,
discharged.  The actual orbicurve certificate remains missing.
-/

import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.Category.FinTopCat
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Separation.Basic
import Iut.Foundations.SourceContinuousAnabelioid
import Iut.Foundations.Orbicurve
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open CategoryTheory
open scoped FintypeCatDiscrete
open scoped Pseudofunctor.StrongTrans

namespace LeanFormal.IUT.XiFPaper.S1737FundamentalGroupFromGaloisActual

/-! ## 1. The canonical action on the underlying finite set of an action -/

/-- The `G`-action on `X.V` delivered by `X.ρ`, stated at the exact object
`(Action.forget FintypeCat G).obj X`.  This is the canonical action, not new
data.  It is needed because `IsFundamentalGroup` asks for a `MulAction` on
`F.obj X`, while Mathlib's `Action.instMulAction` is stated on `X.V`. -/
instance s1737ActionForgetMulAction (G : Type) [Group G]
    (X : Action FintypeCat.{0} G) :
    MulAction G ((Action.forget FintypeCat.{0} G).obj X).obj :=
  inferInstanceAs (MulAction G X.V)

/-- The action of `G` on the fibers of `Action.forget FintypeCat G` is natural
in the categorical variable.  This is the `comm` field of an `Action.Hom`. -/
instance s1737ActionForgetIsNaturalSMul (G : Type) [Group G] :
    PreGaloisCategory.IsNaturalSMul (Action.forget FintypeCat.{0} G) G where
  naturality g {X Y} f x := by
    change f.hom ((X.ρ g).hom x) = (Y.ρ g).hom (f.hom x)
    exact ConcreteCategory.congr_hom (f.comm g) x

/-! ## 2. The exact continuity hypothesis for the full action category -/

/-- Every finite action of `G` is continuous for the given topology on `G`.
Equivalently, every point stabilizer in every finite action is open.  This
is exactly the hypothesis needed for the `continuous_smul` field of
`PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat G) G`. -/
def S1737AllFiniteActionsContinuous (G : Type) [Group G]
    [TopologicalSpace G] : Prop :=
  ∀ X : Action FintypeCat.{0} G, Action.IsContinuous X

/-- Every finite-index subgroup of `G` is open.  This is the group-theoretic
form of `S1737AllFiniteActionsContinuous`: a finite-index subgroup `H` is
the stabilizer of the identity coset in the finite `G`-set `G / H`. -/
def S1737EveryFiniteIndexSubgroupOpen (G : Type) [Group G]
    [TopologicalSpace G] : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex → IsOpen (H : Set G)

/-- Conditional form of the literal target.  This is a complete proof of
`IsFundamentalGroup (Action.forget FintypeCat G) G` from the one missing
continuity hypothesis.  The proofs of naturality, transitivity on Galois
objects, and faithfulness are unconditional. -/
theorem S1737ActionForget_isFundamentalGroup_of_allContinuous
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hcont : S1737AllFiniteActionsContinuous G) :
    PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G) G where
  naturality := s1737ActionForgetIsNaturalSMul G |>.naturality
  transitive_of_isGalois X := by
    intro hGalois
    letI := hGalois
    exact FintypeCat.Action.pretransitive_of_isConnected G X
  continuous_smul X := hcont X
  non_trivial' g h :=
    Iut.continuousAction_nontrivial G g (fun X x => h X.obj x)

/-- From continuity of all finite actions, every finite-index subgroup is
open: take the quotient `G / H`, whose identity coset has stabilizer `H`. -/
theorem S1737EveryFiniteIndexSubgroupOpen_of_allContinuous
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : S1737AllFiniteActionsContinuous G) :
    S1737EveryFiniteIndexSubgroupOpen G := by
  intro H hH
  letI : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  let X : Action FintypeCat.{0} G := G ⧸ₐ H
  have hX : Action.IsContinuous X := h X
  have hX' : ContinuousSMul G X.V := hX
  let x0 : X.V := ((1 : G) : G ⧸ H)
  have hstab : IsOpen (MulAction.stabilizer G x0 : Set G) := by
    haveI : DiscreteTopology X.V := inferInstance
    exact stabilizer_isOpen G x0
  change IsOpen (MulAction.stabilizer G ((1 : G) : G ⧸ H) : Set G) at hstab
  rw [MulAction.stabilizer_quotient] at hstab
  exact hstab

/-- Conversely, if every finite-index subgroup is open, every finite action is
continuous: each point stabilizer has finite index because its orbit is
finite. -/
theorem S1737AllFiniteActionsContinuous_of_everyFiniteIndexOpen
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : S1737EveryFiniteIndexSubgroupOpen G) :
    S1737AllFiniteActionsContinuous G := by
  intro X
  change ContinuousSMul G X.V
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  haveI : Finite (G ⧸ MulAction.stabilizer G x) :=
    (Equiv.finite_iff (MulAction.orbitEquivQuotientStabilizer G x)).mp inferInstance
  exact h (MulAction.stabilizer G x) (Subgroup.finiteIndex_of_finite_quotient)

/-- The exact group-theoretic characterization of the missing hypothesis. -/
theorem S1737AllFiniteActionsContinuous_iff_everyFiniteIndexOpen
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    S1737AllFiniteActionsContinuous G ↔
      S1737EveryFiniteIndexSubgroupOpen G :=
  ⟨S1737EveryFiniteIndexSubgroupOpen_of_allContinuous G,
   S1737AllFiniteActionsContinuous_of_everyFiniteIndexOpen G⟩

/-- Conditional form of the literal target with the group-theoretic
hypothesis "every finite-index subgroup is open". -/
theorem S1737ActionForget_isFundamentalGroup_of_everyFiniteIndexOpen
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h : S1737EveryFiniteIndexSubgroupOpen G) :
    PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G) G :=
  S1737ActionForget_isFundamentalGroup_of_allContinuous G
    ((S1737AllFiniteActionsContinuous_iff_everyFiniteIndexOpen G).mpr h)

/-- Conversely, `IsFundamentalGroup (Action.forget FintypeCat G) G` forces
every finite action to be continuous: this is literally its
`continuous_smul` field. -/
theorem S1737AllFiniteActionsContinuous_of_isFundamentalGroup
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G]
    (h : PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G) G) :
    S1737AllFiniteActionsContinuous G := by
  intro X
  exact h.continuous_smul X

/-- The full-action statement is exactly equivalent to the continuity of all
finite actions.  This is the precise condition boundary of S1737. -/
theorem S1737ActionForget_isFundamentalGroup_iff_allContinuous
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G) G ↔
      S1737AllFiniteActionsContinuous G :=
  ⟨S1737AllFiniteActionsContinuous_of_isFundamentalGroup G,
   S1737ActionForget_isFundamentalGroup_of_allContinuous G⟩

/-- In the finite case the missing hypothesis is discharged: a finite T1
topological group is discrete, so every stabilizer is open. -/
theorem S1737AllFiniteActionsContinuous_of_finite
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Finite G] [T1Space G] :
    S1737AllFiniteActionsContinuous G := by
  intro X
  change ContinuousSMul G X.V
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  exact isOpen_discrete _

/-- The literal full-action theorem for a finite (in particular discrete)
profinite group. -/
theorem S1737ActionForget_isFundamentalGroup_of_finite
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Finite G] [T1Space G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] :
    PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G) G :=
  S1737ActionForget_isFundamentalGroup_of_allContinuous G
    (S1737AllFiniteActionsContinuous_of_finite G)

/-! ## 3. The actual profinite fundamental group: continuous finite G-sets -/

/-- The unconditional theorem for the actual Galois category `B(G)` of finite
continuous `G`-sets: the original profinite group `G` is the fundamental
group of the underlying finite-set fiber functor. -/
theorem S1737ContinuousAction_isFundamentalGroup (G : ProfiniteGrp.{0}) :
    PreGaloisCategory.IsFundamentalGroup (Iut.continuousActionFiber G) G :=
  Iut.continuousAction_isFundamentalGroup G

/-- The actual profinite fundamental-group certificate, packaged as an
`EtaleFundamentalGroup` with `Cover = ContAction FintypeCat G` and with the
original group `G`.  All fields are real: the Galois category, the fiber
functor, the action, and the fundamental-group proof are the ones proved in
`Iut.SourceContinuousAnabelioid`. -/
noncomputable def S1737ContinuousEtaleFundamentalGroup (G : ProfiniteGrp.{0}) :
    Iut.EtaleFundamentalGroup where
  Cover := ContAction FintypeCat.{0} G
  coverCategory := inferInstance
  galoisCategory := Iut.continuousAction_galoisCategory G
  fiber := Iut.continuousActionFiber G
  fiberFunctor := Iut.continuousAction_fiberFunctor G
  group := G
  action := Iut.continuousActionFiber_mulAction G
  isFundamentalGroup := Iut.continuousAction_isFundamentalGroup G

/-! ## 4. The absolute Galois group specialization -/

/-- The absolute Galois group of `F`, as an actual profinite group. -/
abbrev S1737AbsoluteGalois (F : Type) [Field F] : ProfiniteGrp.{0} :=
  Iut.AbsoluteGaloisProfinite F

/-- The actual theorem for `G = AbsoluteGaloisProfinite F`, in the correct
continuous finite-set category. -/
theorem S1737AbsoluteGalois_continuousAction_isFundamentalGroup
    (F : Type) [Field F] :
    PreGaloisCategory.IsFundamentalGroup
      (Iut.continuousActionFiber (S1737AbsoluteGalois F))
      (S1737AbsoluteGalois F) :=
  Iut.continuousAction_isFundamentalGroup _

/-- The actual `EtaleFundamentalGroup` certificate for the absolute Galois
group of `F`. -/
noncomputable def S1737AbsoluteGaloisContinuousEtaleFundamentalGroup
    (F : Type) [Field F] : Iut.EtaleFundamentalGroup :=
  S1737ContinuousEtaleFundamentalGroup (S1737AbsoluteGalois F)

/-- The exact missing condition for the LITERAL full-action statement at
`G = AbsoluteGaloisProfinite F`: every finite `G`-action must be
continuous.  This is not supplied by Mathlib for a general field.  For an
infinite profinite group with a non-open finite-index subgroup it is false;
for finite `G` it is discharged above. -/
def S1737AbsoluteGaloisActionForgetMissing (F : Type) [Field F] : Prop :=
  S1737AllFiniteActionsContinuous (S1737AbsoluteGalois F)

/-- The same missing condition in group-theoretic form: every finite-index
subgroup of the absolute Galois group is open. -/
def S1737AbsoluteGaloisEveryFiniteIndexSubgroupOpen
    (F : Type) [Field F] : Prop :=
  S1737EveryFiniteIndexSubgroupOpen (S1737AbsoluteGalois F)

/-- The continuity missing condition and the finite-index-open condition are
equivalent at the absolute Galois group. -/
theorem S1737AbsoluteGaloisActionForgetMissing_iff_everyFiniteIndexOpen
    (F : Type) [Field F] :
    S1737AbsoluteGaloisActionForgetMissing F ↔
      S1737AbsoluteGaloisEveryFiniteIndexSubgroupOpen F :=
  S1737AllFiniteActionsContinuous_iff_everyFiniteIndexOpen _

/-- Conditional proof of the literal full-action statement at
`G = AbsoluteGaloisProfinite F`, with the exact missing hypothesis. -/
theorem S1737AbsoluteGalois_actionForget_isFundamentalGroup_of_allContinuous
    (F : Type) [Field F]
    (h : S1737AbsoluteGaloisActionForgetMissing F) :
    PreGaloisCategory.IsFundamentalGroup
      (Action.forget FintypeCat.{0} (S1737AbsoluteGalois F))
      (S1737AbsoluteGalois F) :=
  S1737ActionForget_isFundamentalGroup_of_allContinuous _ h

/-- The literal full-action statement is equivalent to the missing
continuity condition, even at `G = AbsoluteGaloisProfinite F`. -/
theorem S1737AbsoluteGalois_actionForget_isFundamentalGroup_iff
    (F : Type) [Field F] :
    PreGaloisCategory.IsFundamentalGroup
      (Action.forget FintypeCat.{0} (S1737AbsoluteGalois F))
      (S1737AbsoluteGalois F) ↔
      S1737AbsoluteGaloisActionForgetMissing F :=
  S1737ActionForget_isFundamentalGroup_iff_allContinuous _

/-- For the FULL action category, Mathlib's available fundamental group is
`Aut (Action.forget FintypeCat G)`, not the abstract group `G`.  This is what
is unconditionally proved by Mathlib's Galois-category API. -/
theorem S1737ActionForget_aut_isFundamentalGroup (G : Type) [Group G] :
    PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G)
      (Aut (Action.forget FintypeCat.{0} G)) :=
  inferInstance

/-! ## 5. The `OrbicurveEtaleFundamentalGroup` assembly fields -/

/-- The two base fields of `OrbicurveEtaleFundamentalGroup`, isolated.  These
are exactly the fields that can be filled for the representable S1726
orbicurve. -/
structure S1737OrbicurveBaseFields (F : Type) [Field F]
    (X : Iut.HyperbolicOrbicurve F) where
  baseScheme : Iut.SchemeOverField F
  basePoint :
    Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F baseScheme)
      X.stack.fiber

namespace S1737OrbicurveBaseFields

variable {F : Type} [Field F] {X : Iut.HyperbolicOrbicurve F}

/-- Every actual `OrbicurveEtaleFundamentalGroup` supplies the base fields. -/
noncomputable def ofEtalePi {G : ProfiniteGrp.{0}}
    (D : Iut.OrbicurveEtaleFundamentalGroup X G) :
    S1737OrbicurveBaseFields F X where
  baseScheme := D.baseScheme
  basePoint := D.basePoint

end S1737OrbicurveBaseFields

/-- The eleven fields requested for the orbicurve assembly, with their exact
types (the target has five further coherence fields: `coverMorphism_over`,
`coverMorphism_bijective`, `coverMorphism_id`, `coverMorphism_comp`, and
`fiberIdentification_natural`).  This structure is the field list; only the
base fields are inhabited for S1726. -/
structure S1737OrbicurveFields (F : Type) [Field F]
    (X : Iut.HyperbolicOrbicurve F) (G : ProfiniteGrp.{0}) where
  coverCategory : Category.{0} (Iut.OrbicurveFiniteEtaleCover X)
  galoisCategory :
    letI := coverCategory
    @GaloisCategory (Iut.OrbicurveFiniteEtaleCover X) coverCategory
  baseScheme : Iut.SchemeOverField F
  basePoint :
    Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F baseScheme)
      X.stack.fiber
  fiber :
    letI := coverCategory
    Iut.OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{0}
  fiberFunctor :
    letI := coverCategory
    letI := galoisCategory
    PreGaloisCategory.FiberFunctor fiber
  coverMorphism :
    letI := coverCategory
    ∀ {source target : Iut.OrbicurveFiniteEtaleCover X},
      (source ⟶ target) → source.source.Hom target.source
  geometricFiberFintype :
    ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
      Fintype
        (Iut.OrbicurveFiniteEtaleCover.GeometricFiber
          baseScheme basePoint cover)
  fiberIdentification :
    ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
      (fiber.obj cover).obj ≃
        Iut.OrbicurveFiniteEtaleCover.GeometricFiber
          baseScheme basePoint cover
  action :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
      MulAction G (fiber.obj cover)
  isFundamentalGroup :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    letI (cover : Iut.OrbicurveFiniteEtaleCover X) := action cover
    PreGaloisCategory.IsFundamentalGroup fiber G

namespace S1737OrbicurveFields

variable {F : Type} [Field F] {X : Iut.HyperbolicOrbicurve F}
variable {G : ProfiniteGrp.{0}}

/-- Every actual `OrbicurveEtaleFundamentalGroup` supplies all requested
fields.  This is the projection from the full certificate, not a
construction of it. -/
noncomputable def ofEtalePi (D : Iut.OrbicurveEtaleFundamentalGroup X G) :
    S1737OrbicurveFields F X G where
  coverCategory := D.coverCategory
  galoisCategory := D.galoisCategory
  baseScheme := D.baseScheme
  basePoint := D.basePoint
  fiber := D.fiber
  fiberFunctor := D.fiberFunctor
  coverMorphism := D.coverMorphism
  geometricFiberFintype := D.geometricFiberFintype
  fiberIdentification := D.fiberIdentification
  action := D.action
  isFundamentalGroup := D.isFundamentalGroup

end S1737OrbicurveFields

/-- The exact first missing field of the orbicurve certificate: a small
category structure on the actual Type 1 cover type. -/
def S1737OrbicurveCoverCategoryMissing (F : Type) [Field F]
    (X : Iut.HyperbolicOrbicurve F) : Type 1 :=
  Category.{0} (Iut.OrbicurveFiniteEtaleCover X)

/-- The actual target implies the missing small category field.  This is the
precise first obstruction, not a convenient restatement. -/
theorem S1737OrbicurveCoverCategoryMissing_of_etalePi
    {F : Type} [Field F] {X : Iut.HyperbolicOrbicurve F} {G : ProfiniteGrp.{0}}
    (D : Iut.OrbicurveEtaleFundamentalGroup X G) :
    Nonempty (S1737OrbicurveCoverCategoryMissing F X) :=
  ⟨D.coverCategory⟩

/-! ## 6. The S1726 representable orbicurve: filled base fields -/

open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

/-- The underlying finite type of the S1726 orbicurve. -/
abbrev S1737S1726Cover : Type 1 :=
  Iut.OrbicurveFiniteEtaleCover S1726Orbicurve

/-- The actual hom type of the S1726 cover category is Type 1.  A
`Category.{0}` on this object type needs a Type 0 hom carrier with an
equivalence to this hom type; S1728 shows that such a carrier is the exact
missing smallness input. -/
abbrev S1737S1726CoverMap (A B : S1737S1726Cover) : Type 1 :=
  Iut.OrbicurveFiniteEtaleCoverMap A B

/-- The S1726 base scheme: `Spec R'` over `Spec F'`.  The stack of the S1726
orbicurve is the representable etale pseudofunctor of this scheme, so it is a
genuine geometric base. -/
abbrev S1737S1726BaseScheme : Iut.SchemeOverField S1726K :=
  S1726AffineOver

/-- The actual base point: the identity strong transformation from the
representable pseudofunctor of `S1726AffineOver` to the stack fiber.  This
typechecks because the S1726 stack fiber is definitionally that
representable pseudofunctor. -/
noncomputable def S1737S1726BasePoint :
    Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor S1726K S1737S1726BaseScheme)
      S1726Orbicurve.stack.fiber :=
  Pseudofunctor.StrongTrans.id _

/-- The two fillable `OrbicurveEtaleFundamentalGroup` fields for S1726. -/
noncomputable def S1737S1726BaseFieldsActual :
    S1737OrbicurveBaseFields S1726K S1726Orbicurve where
  baseScheme := S1737S1726BaseScheme
  basePoint := S1737S1726BasePoint

/-- The full target for S1726 supplies the base fields, but no other field is
constructed here. -/
noncomputable def S1737S1726BaseFieldsOfEtalePi
    {G : ProfiniteGrp.{0}}
    (D : Iut.OrbicurveEtaleFundamentalGroup S1726Orbicurve G) :
    S1737OrbicurveBaseFields S1726K S1726Orbicurve :=
  S1737OrbicurveBaseFields.ofEtalePi D

/-! ## 7. Exact missing fields, recorded as types

For `OrbicurveEtaleFundamentalGroup X G` the field-by-field status is:

* `coverCategory`: MISSING.  The type is
  `Category.{0} (OrbicurveFiniteEtaleCover X)`; the actual cover type lives in
  Type 1 and its actual hom type `OrbicurveFiniteEtaleCoverMap` is Type 1.
  S1728 proves that the target implies a small raw cover-map carrier, which is
  not constructed.
* `galoisCategory`: MISSING, and depends on `coverCategory`.
* `baseScheme`, `basePoint`: FILLED for the S1726 representable orbicurve
  (`S1737S1726BaseFieldsActual`).
* `fiber`, `fiberFunctor`: MISSING; no functor from the actual cover type to
  `FintypeCat` is constructed.
* `coverMorphism` and its four coherence fields
  (`coverMorphism_over`, `coverMorphism_bijective`, `coverMorphism_id`,
  `coverMorphism_comp`): MISSING.  A categorical arrow must first be
  realized by an actual strong transformation of stacks.
* `geometricFiberFintype`: MISSING; finiteness of the literal
  `CostructuredArrow` geometric fiber is not proved for an arbitrary cover.
* `fiberIdentification` and `fiberIdentification_natural`: MISSING; no
  equivalence between a chosen fiber functor and the literal geometric fiber
  is constructed.
* `action`, `isFundamentalGroup`: MISSING for the orbicurve.  The generic
  `ContAction` theorem cannot be transported to `OrbicurveFiniteEtaleCover X`
  without the missing Galois correspondence / fiber identification.

Only `baseScheme` and `basePoint` are filled; the other nine requested fields
and the five coherence fields are missing.
-/

/-! ## 7. Exact missing fields, recorded as types -/

/-- The missing `galoisCategory` field, once a cover category is supplied. -/
def S1737OrbicurveGaloisCategoryMissing (F : Type) [Field F]
    (X : Iut.HyperbolicOrbicurve F)
    (C : Category.{0} (Iut.OrbicurveFiniteEtaleCover X)) : Prop :=
  @GaloisCategory (Iut.OrbicurveFiniteEtaleCover X) C

/-- The missing `geometricFiberFintype` field. -/
def S1737OrbicurveGeometricFiberFintypeMissing (F : Type) [Field F]
    (X : Iut.HyperbolicOrbicurve F) (baseScheme : Iut.SchemeOverField F)
    (basePoint :
      Pseudofunctor.StrongTrans
        (Iut.schemeRepresentableEtalePseudofunctor F baseScheme)
        X.stack.fiber) : Type 1 :=
  ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
    Fintype
      (Iut.OrbicurveFiniteEtaleCover.GeometricFiber
        baseScheme basePoint cover)

/-- The missing `fiberIdentification` field, for a given fiber functor. -/
def S1737OrbicurveFiberIdentificationMissing (F : Type) [Field F]
    (X : Iut.HyperbolicOrbicurve F) (baseScheme : Iut.SchemeOverField F)
    (basePoint :
      Pseudofunctor.StrongTrans
        (Iut.schemeRepresentableEtalePseudofunctor F baseScheme)
        X.stack.fiber)
    (fiber : Iut.OrbicurveFiniteEtaleCover X → FintypeCat.{0}) : Type 1 :=
  ∀ cover : Iut.OrbicurveFiniteEtaleCover X,
    (fiber cover).obj ≃
      Iut.OrbicurveFiniteEtaleCover.GeometricFiber
        baseScheme basePoint cover

/-! ## 8. Axiom footprint -/

#check S1737EveryFiniteIndexSubgroupOpen
#check S1737EveryFiniteIndexSubgroupOpen_of_allContinuous
#check S1737AllFiniteActionsContinuous_of_everyFiniteIndexOpen
#check S1737AllFiniteActionsContinuous_iff_everyFiniteIndexOpen
#check S1737ActionForget_isFundamentalGroup_of_everyFiniteIndexOpen
#check S1737AbsoluteGaloisActionForgetMissing_iff_everyFiniteIndexOpen
#check S1737ActionForget_isFundamentalGroup_of_allContinuous
#check S1737ActionForget_isFundamentalGroup_iff_allContinuous
#check S1737ActionForget_isFundamentalGroup_of_finite
#check S1737ContinuousAction_isFundamentalGroup
#check S1737ContinuousEtaleFundamentalGroup
#check S1737AbsoluteGalois_continuousAction_isFundamentalGroup
#check S1737AbsoluteGaloisContinuousEtaleFundamentalGroup
#check S1737AbsoluteGalois_actionForget_isFundamentalGroup_iff
#check S1737ActionForget_aut_isFundamentalGroup
#check S1737OrbicurveBaseFields
#check S1737OrbicurveFields
#check S1737OrbicurveFields.ofEtalePi
#check S1737S1726BaseFieldsActual
#check S1737S1726BaseFieldsOfEtalePi

#print axioms S1737AllFiniteActionsContinuous_iff_everyFiniteIndexOpen
#print axioms S1737ActionForget_isFundamentalGroup_of_everyFiniteIndexOpen
#print axioms S1737AbsoluteGaloisActionForgetMissing_iff_everyFiniteIndexOpen
#print axioms S1737ActionForget_isFundamentalGroup_of_allContinuous
#print axioms S1737ActionForget_isFundamentalGroup_iff_allContinuous
#print axioms S1737ActionForget_isFundamentalGroup_of_finite
#print axioms S1737ContinuousAction_isFundamentalGroup
#print axioms S1737ContinuousEtaleFundamentalGroup
#print axioms S1737AbsoluteGalois_continuousAction_isFundamentalGroup
#print axioms S1737AbsoluteGalois_actionForget_isFundamentalGroup_iff
#print axioms S1737ActionForget_aut_isFundamentalGroup
#print axioms S1737S1726BaseFieldsActual
#print axioms S1737OrbicurveFields.ofEtalePi

end LeanFormal.IUT.XiFPaper.S1737FundamentalGroupFromGaloisActual