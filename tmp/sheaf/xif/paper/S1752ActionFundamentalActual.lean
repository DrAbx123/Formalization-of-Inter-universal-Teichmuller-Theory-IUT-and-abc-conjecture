/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/

import tmp.sheaf.xif.paper.S1737FundamentalGroupFromGaloisActual
import tmp.sheaf.xif.paper.S1741AutFiberActual
import tmp.sheaf.xif.paper.S1751FiniteIndexOpenActual
import Mathlib.FieldTheory.IsSepClosed

/-!
# S1752: the full finite-action category for the absolute Galois group

Let

  F be a field,
  G := Iut.AbsoluteGaloisProfinite F = profiniteGalGrp F (SeparableClosure F),

and let Action FintypeCat.{0} G be the category of *all* finite G-sets
(with no continuity condition).  This file addresses the literal S1737 target

  PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G) G.

## Result

The Galois-category part is unconditional: Action FintypeCat.{0} G is a
Mathlib Galois category and the forgetful functor is a fibre functor
(S1752ActionGaloisCategoryCertificate).  The fundamental-group part is
*conditional*, because the continuous_smul field of IsFundamentalGroup
asks that every finite action of the profinite group G be continuous.

The exact missing hypothesis is

  S1752ActionForgetMissing F := S1737AllFiniteActionsContinuous G,

equivalently every finite-index subgroup of G is open
(S1752ActionForgetMissing_iff_everyFiniteIndexOpen).  This is the strong
completeness property of G.  It is not a consequence of compactness: a
compact Hausdorff totally disconnected group can have a non-open finite-index
subgroup.  Mathlib supplies neither the condition nor its negation for a
general absolute Galois group.

Task S1751 is now present in the tree.  It identifies the missing condition
with S1751Target (S1752ActionForgetMissing_iff_S1751Target) and proves that
a non-open finite-index subgroup refutes the literal target.  Its number-field
counterexample is recorded there as the external proposition
S1751NonOpenSubgroupMissing, not as a Lean theorem: the file does not
formalize the Kummer-theoretic quotient Gal(Qbar/Q) -> product Z/2 or the
choice construction of a non-open index-two subgroup.  Accordingly, the
literal target is not unconditionally established here (and, by the cited
Milne result used in S1751, it is false for number fields).  This file
therefore proves the conditional theorem, the exact equivalence, and the
comparison with Aut, and composes with S1751's input: if
S1751NonOpenSubgroupMissing F holds, the literal target is false
(S1752ActionForget_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing).

From the conditional theorem we build a genuine
Iut.EtaleFundamentalGroup with

  Cover = Action FintypeCat.{0} G,
  fiber = Action.forget FintypeCat.{0} G,
  group = G.

For a separably closed field F the absolute Galois group is trivial, so the
missing condition is discharged and the EtaleFundamentalGroup is
unconditional (S1752ActionEtaleFundamentalGroup_of_isSepClosed).  The same
holds whenever the absolute Galois group is finite, using S1737's finite
case.  For number fields the missing condition is not merely unproved but
false by S1751's cited counterexample, so no unconditional
EtaleFundamentalGroup with group G exists there.

No sorry, admit, new axiom, Shrink, ULift, PUnit, fake group,
fake action or fake category is used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open CategoryTheory
open scoped FintypeCatDiscrete

namespace LeanFormal.IUT.XiFPaper.S1752ActionFundamentalActual

open LeanFormal.IUT.XiFPaper.S1737FundamentalGroupFromGaloisActual
open LeanFormal.IUT.XiFPaper.S1751FiniteIndexOpenActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-! ## 1. The group, the action category and the forgetful fibre functor -/

/-- The absolute Galois group of F, as the actual profinite group of S1737. -/
abbrev S1752G (F : Type) [Field F] : ProfiniteGrp.{0} :=
  Iut.AbsoluteGaloisProfinite F

/-- The category of all finite G-sets (no continuity condition). -/
abbrev S1752ActionCategory (F : Type) [Field F] : Type 1 :=
  Action FintypeCat.{0} (S1752G F)

/-- The forgetful functor to finite sets, the fibre functor of the action
category. -/
abbrev S1752ActionForget (F : Type) [Field F] :
    S1752ActionCategory F ⥤ FintypeCat.{0} :=
  Action.forget FintypeCat.{0} (S1752G F)

/-- The canonical action of G on the fibre of the forgetful functor, i.e. on
the underlying finite set of a finite G-set.  This is the actual
Action.instMulAction, restated at the object (Action.forget ...).obj X. -/
@[implicit_reducible]
def S1752ActionForgetMulAction (F : Type) [Field F]
    (X : S1752ActionCategory F) :
    MulAction (S1752G F) ((S1752ActionForget F).obj X) :=
  S1741.actionForgetMulAction (S1752G F) X

/-- **Unconditional Galois-category certificate**: Action FintypeCat.{0} G is
a Galois category and the forgetful functor is a fibre functor.  These are
Mathlib's instances, not assumptions. -/
structure S1752ActionGaloisCategoryCertificate (F : Type) [Field F] where
  /-- The Galois-category structure on all finite G-sets. -/
  galoisCategory : GaloisCategory (S1752ActionCategory F)
  /-- The forgetful functor is a fibre functor. -/
  fiberFunctor : PreGaloisCategory.FiberFunctor (S1752ActionForget F)

/-- The unconditional Galois-category certificate, built from Mathlib. -/
theorem S1752ActionGaloisCategoryCertificate.of
    (F : Type) [Field F] : S1752ActionGaloisCategoryCertificate F where
  galoisCategory := inferInstance
  fiberFunctor := inferInstance

/-- **Unconditional data-carrying Galois-category certificate**: the actual
category structure on Action FintypeCat.{0} G, the Galois-category proof,
the actual forgetful fibre functor, and its fibre-functor proof.  Unlike the
Prop-level certificate above, this structure stores the category and functor
data themselves. -/
structure S1752ActionGaloisCategoryData (F : Type) [Field F] where
  /-- The category structure on all finite G-sets. -/
  coverCategory : Category.{0} (S1752ActionCategory F)
  /-- The Galois-category proof for this category structure. -/
  galoisCategory : @GaloisCategory (S1752ActionCategory F) coverCategory
  /-- The forgetful fibre functor. -/
  fiber : S1752ActionCategory F ⥤ FintypeCat.{0}
  /-- The fibre-functor proof for the forgetful functor. -/
  fiberFunctor :
    letI := coverCategory
    letI := galoisCategory
    PreGaloisCategory.FiberFunctor fiber

/-- The unconditional data-carrying Galois-category certificate, built from
Mathlib's instances. -/
noncomputable def S1752ActionGaloisCategoryData.of
    (F : Type) [Field F] : S1752ActionGaloisCategoryData F where
  coverCategory := inferInstance
  galoisCategory := inferInstance
  fiber := S1752ActionForget F
  fiberFunctor := inferInstance

/-- The unconditional Aut-based fundamental-group certificate.  The group is
Aut (Action.forget ...), which lives in ProfiniteGrp.{1}; this is why it
cannot be the group field of Iut.EtaleFundamentalGroup (that field is
ProfiniteGrp.{u} with Cover : Type (u+1)). -/
noncomputable def S1752ActionAutCertificate (F : Type) [Field F] :
    S1741.FiberFundamentalGroupCertificate
      (S1752ActionCategory F) (S1752ActionForget F)
      (S1741.actionAutProfiniteGrp (S1752G F)) :=
  S1741.actionAutCertificate (S1752G F)

/-! ## 2. The exact missing condition -/

/-- The precise missing condition: every finite action of the absolute Galois
group is continuous.  Equivalently, every finite-index subgroup is open. -/
def S1752ActionForgetMissing (F : Type) [Field F] : Prop :=
  S1737AllFiniteActionsContinuous (S1752G F)

/-- The group-theoretic form of the missing condition: every finite-index
subgroup of the absolute Galois group is open. -/
def S1752EveryFiniteIndexSubgroupOpen (F : Type) [Field F] : Prop :=
  S1737EveryFiniteIndexSubgroupOpen (S1752G F)

/-- The two forms of the missing condition are equivalent. -/
theorem S1752ActionForgetMissing_iff_everyFiniteIndexOpen
    (F : Type) [Field F] :
    S1752ActionForgetMissing F ↔ S1752EveryFiniteIndexSubgroupOpen F :=
  S1737AllFiniteActionsContinuous_iff_everyFiniteIndexOpen (S1752G F)

/-- The same missing condition, written with the S1737 name specialised to
AbsoluteGaloisProfinite F.  This is the interface that a successful S1751
would supply. -/
theorem S1752ActionForgetMissing_iff_S1737
    (F : Type) [Field F] :
    S1752ActionForgetMissing F ↔ S1737AbsoluteGaloisActionForgetMissing F :=
  Iff.rfl

/-- The S1737 group-theoretic form at this concrete group. -/
theorem S1752EveryFiniteIndexSubgroupOpen_iff_S1737
    (F : Type) [Field F] :
    S1752EveryFiniteIndexSubgroupOpen F ↔
      S1737AbsoluteGaloisEveryFiniteIndexSubgroupOpen F :=
  Iff.rfl


/-! ### 2.1. Relation with S1751 -/

/-- The S1751 group-theoretic target is exactly the missing condition of this
file.  Both are the S1737 condition at Iut.AbsoluteGaloisProfinite F. -/
theorem S1752ActionForgetMissing_iff_S1751Target
    (F : Type) [Field F] :
    S1752ActionForgetMissing F ↔ S1751Target F := by
  rw [S1752ActionForgetMissing_iff_everyFiniteIndexOpen]
  exact Iff.rfl

/-- The negation of the missing condition is exactly S1751's refutation. -/
theorem S1752ActionForgetMissing_false_iff_S1751Refutation
    (F : Type) [Field F] :
    (¬ S1752ActionForgetMissing F) ↔ S1751Refutation F := by
  rw [S1752ActionForgetMissing_iff_everyFiniteIndexOpen]
  exact Iff.rfl

/-- S1751's external number-theoretic input rules out the missing condition. -/
theorem S1752ActionForgetMissing_false_of_S1751NonOpenSubgroupMissing
    (F : Type) [Field F] (h : S1751NonOpenSubgroupMissing F) :
    ¬ S1752ActionForgetMissing F := by
  intro hmissing
  exact (S1751Refutation_of_missing F h)
    ((S1752ActionForgetMissing_iff_everyFiniteIndexOpen F).mp hmissing)

/-! ## 3. The conditional fundamental-group theorem -/

/-- **The literal S1737 target at G = AbsoluteGaloisProfinite F**, conditional
only on the exact continuity hypothesis.  The proof is S1737's real proof; no
step is assumed. -/
theorem S1752ActionForget_isFundamentalGroup
    (F : Type) [Field F] (h : S1752ActionForgetMissing F) :
    PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) :=
  S1737ActionForget_isFundamentalGroup_of_allContinuous (S1752G F) h

/-- The same theorem with the action instance made explicit, so that it can be
used directly as the isFundamentalGroup field of an
Iut.EtaleFundamentalGroup. -/
theorem S1752ActionForget_isFundamentalGroup_letI
    (F : Type) [Field F] (h : S1752ActionForgetMissing F) :
    letI (X : S1752ActionCategory F) := S1752ActionForgetMulAction F X
    PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) := by
  letI (X : S1752ActionCategory F) := S1752ActionForgetMulAction F X
  exact S1752ActionForget_isFundamentalGroup F h

/-- **The exact characterization**: the literal target holds if and only if
every finite action of the absolute Galois group is continuous. -/
theorem S1752ActionForget_isFundamentalGroup_iff_missing
    (F : Type) [Field F] :
    PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) ↔
        S1752ActionForgetMissing F :=
  S1737ActionForget_isFundamentalGroup_iff_allContinuous (S1752G F)

/-- If the missing condition fails, the literal target is false (not merely
unproved).  This is the form in which a successful S1751 refutation of the
continuity condition would settle the literal statement negatively. -/
theorem S1752ActionForget_not_isFundamentalGroup_of_not_missing
    (F : Type) [Field F] (h : ¬ S1752ActionForgetMissing F) :
    ¬ PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) :=
  fun hfund => h
    ((S1752ActionForget_isFundamentalGroup_iff_missing F).mp hfund)

/-- A non-open finite-index subgroup of the absolute Galois group refutes the
literal target. -/
theorem S1752ActionForget_not_isFundamentalGroup_of_nonOpen
    (F : Type) [Field F]
    (H : Subgroup (S1752G F)) [H.FiniteIndex]
    (hH : ¬ IsOpen (H : Set (S1752G F))) :
    ¬ PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) := by
  apply S1752ActionForget_not_isFundamentalGroup_of_not_missing F
  intro hmissing
  exact hH ((S1752ActionForgetMissing_iff_everyFiniteIndexOpen F).mp
    hmissing H ‹H.FiniteIndex›)

/-- Consequently, S1751's external input refutes the literal S1737 target at
Iut.AbsoluteGaloisProfinite F.  The input itself is not asserted here. -/
theorem S1752ActionForget_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing
    (F : Type) [Field F] (h : S1751NonOpenSubgroupMissing F) :
    ¬ PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) :=
  S1752ActionForget_not_isFundamentalGroup_of_not_missing F
    (S1752ActionForgetMissing_false_of_S1751NonOpenSubgroupMissing F h)

/-- The conditional target from the group-theoretic form of the missing
condition: every finite-index subgroup of the absolute Galois group is
open. -/
theorem S1752ActionForget_isFundamentalGroup_of_everyFiniteIndexOpen
    (F : Type) [Field F] (h : S1752EveryFiniteIndexSubgroupOpen F) :
    PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) :=
  S1752ActionForget_isFundamentalGroup F
    ((S1752ActionForgetMissing_iff_everyFiniteIndexOpen F).mpr h)

/-- The literal target directly from S1751's group-theoretic target. -/
theorem S1752ActionForget_isFundamentalGroup_of_S1751Target
    (F : Type) [Field F] (h : S1751Target F) :
    PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) :=
  S1752ActionForget_isFundamentalGroup_of_everyFiniteIndexOpen F h

/-- The conditional target directly from the S1741 comparison datum: a
continuous group isomorphism G to Aut F whose action is the canonical one.
This is the form in which a successful S1751 could supply the input. -/
theorem S1752ActionForget_isFundamentalGroup_of_continuousMulEquiv
    (F : Type) [Field F]
    (e : S1752G F ≃ₜ* Aut (S1752ActionForget F))
    (hact : ∀ (g : S1752G F) (X : S1752ActionCategory F)
      (x : (S1752ActionForget F).obj X),
      (e g).hom.app X x = g • x) :
    PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) := by
  letI (X : S1752ActionCategory F) := S1752ActionForgetMulAction F X
  exact S1741.isFundamentalGroup_of_continuousMulEquiv
    (F := S1752ActionForget F) (G := S1752G F) e hact

/-- The exact S1737 target name at this group, in conditional form. -/
theorem S1737ActionForget_isFundamentalGroup
    (F : Type) [Field F] (h : S1752ActionForgetMissing F) :
    PreGaloisCategory.IsFundamentalGroup
      (Action.forget FintypeCat.{0} (S1752G F)) (S1752G F) :=
  S1752ActionForget_isFundamentalGroup F h

/-- The same equivalence with the explicit action instance. -/
theorem S1752ActionForget_isFundamentalGroup_iff_missing_letI
    (F : Type) [Field F] :
    (letI (X : S1752ActionCategory F) := S1752ActionForgetMulAction F X
     PreGaloisCategory.IsFundamentalGroup
       (S1752ActionForget F) (S1752G F)) ↔
        S1752ActionForgetMissing F := by
  letI (X : S1752ActionCategory F) := S1752ActionForgetMulAction F X
  exact S1752ActionForget_isFundamentalGroup_iff_missing F

/-! ## 4. The continuous comparison with Aut -/

/-- Under the exact missing hypothesis, the group G is continuously
isomorphic to the automorphism group of the forgetful fibre functor.  This is
the comparison datum isolated in S1741. -/
noncomputable def S1752ActionForgetToAutContinuous
    (F : Type) [Field F] (h : S1752ActionForgetMissing F) :
    S1752G F ≃ₜ* Aut (S1752ActionForget F) := by
  letI (X : S1752ActionCategory F) := S1752ActionForgetMulAction F X
  letI : PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) :=
    S1752ActionForget_isFundamentalGroup F h
  let e : S1752G F ≃* Aut (S1752ActionForget F) :=
    PreGaloisCategory.toAutMulEquiv (S1752ActionForget F) (S1752G F)
  let hh : IsHomeomorph e :=
    PreGaloisCategory.toAutMulEquiv_isHomeomorph
      (S1752ActionForget F) (S1752G F)
  exact ContinuousMulEquiv.mk' (hh.homeomorph e) (fun x y => e.map_mul x y)

/-- The comparison map is the canonical evaluation action: its value on a
finite G-set is the actual G-action. -/
theorem S1752ActionForgetToAutContinuous_smul
    (F : Type) [Field F] (h : S1752ActionForgetMissing F)
    (g : S1752G F) (X : S1752ActionCategory F)
    (x : (S1752ActionForget F).obj X) :
    (S1752ActionForgetToAutContinuous F h g).hom.app X x = g • x := by
  letI (X : S1752ActionCategory F) := S1752ActionForgetMulAction F X
  letI : PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) :=
    S1752ActionForget_isFundamentalGroup F h
  exact PreGaloisCategory.toAut_hom_app_apply (S1752ActionForget F) g x

/-- **The exact comparison-datum characterization**: the missing condition is
equivalent to the existence of a continuous group isomorphism G to Aut F
whose action is the canonical one.  This is exactly the S1741 interface. -/
theorem S1752ActionForgetMissing_iff_exists_continuousMulEquiv
    (F : Type) [Field F] :
    S1752ActionForgetMissing F ↔
      ∃ e : S1752G F ≃ₜ* Aut (S1752ActionForget F),
        ∀ (g : S1752G F) (X : S1752ActionCategory F)
          (x : (S1752ActionForget F).obj X),
          (e g).hom.app X x = g • x := by
  constructor
  · intro h
    exact ⟨S1752ActionForgetToAutContinuous F h,
      S1752ActionForgetToAutContinuous_smul F h⟩
  · rintro ⟨e, hact⟩
    letI (X : S1752ActionCategory F) := S1752ActionForgetMulAction F X
    have hFG : PreGaloisCategory.IsFundamentalGroup
        (S1752ActionForget F) (S1752G F) :=
      S1741.isFundamentalGroup_of_continuousMulEquiv
        (F := S1752ActionForget F) (G := S1752G F) e hact
    exact (S1752ActionForget_isFundamentalGroup_iff_missing F).mp hFG

/-! ## 5. Packaging as an EtaleFundamentalGroup -/

/-- **Conditional Iut.EtaleFundamentalGroup** for the full finite-action
category.  All fields are real: the Galois category and fibre functor are
Mathlib's, the action is the actual action on finite G-sets, and the
fundamental-group field is the conditional theorem above. -/
noncomputable def S1752ActionEtaleFundamentalGroup
    (F : Type) [Field F] (h : S1752ActionForgetMissing F) :
    Iut.EtaleFundamentalGroup where
  Cover := S1752ActionCategory F
  coverCategory := inferInstance
  galoisCategory := inferInstance
  fiber := S1752ActionForget F
  fiberFunctor := inferInstance
  group := S1752G F
  action := S1752ActionForgetMulAction F
  isFundamentalGroup := S1752ActionForget_isFundamentalGroup_letI F h

@[simp]
theorem S1752ActionEtaleFundamentalGroup_cover
    (F : Type) [Field F] (h : S1752ActionForgetMissing F) :
    (S1752ActionEtaleFundamentalGroup F h).Cover = S1752ActionCategory F :=
  rfl

@[simp]
theorem S1752ActionEtaleFundamentalGroup_group
    (F : Type) [Field F] (h : S1752ActionForgetMissing F) :
    (S1752ActionEtaleFundamentalGroup F h).group = S1752G F :=
  rfl

@[simp]
theorem S1752ActionEtaleFundamentalGroup_fiber
    (F : Type) [Field F] (h : S1752ActionForgetMissing F) :
    (S1752ActionEtaleFundamentalGroup F h).fiber = S1752ActionForget F :=
  rfl

/-- Conditional EtaleFundamentalGroup from the group-theoretic form of the
missing condition (the form a successful S1751 would supply). -/
noncomputable def S1752ActionEtaleFundamentalGroup_of_everyFiniteIndexOpen
    (F : Type) [Field F] (h : S1752EveryFiniteIndexSubgroupOpen F) :
    Iut.EtaleFundamentalGroup :=
  S1752ActionEtaleFundamentalGroup F
    ((S1752ActionForgetMissing_iff_everyFiniteIndexOpen F).mpr h)

/-- Conditional EtaleFundamentalGroup from the S1741 comparison datum
G ≃ₜ* Aut F with the canonical action. -/
noncomputable def S1752ActionEtaleFundamentalGroup_of_continuousMulEquiv
    (F : Type) [Field F]
    (e : S1752G F ≃ₜ* Aut (S1752ActionForget F))
    (hact : ∀ (g : S1752G F) (X : S1752ActionCategory F)
      (x : (S1752ActionForget F).obj X),
      (e g).hom.app X x = g • x) :
    Iut.EtaleFundamentalGroup :=
  S1752ActionEtaleFundamentalGroup F
    ((S1752ActionForgetMissing_iff_exists_continuousMulEquiv F).mpr ⟨e, hact⟩)


/-- At the actual IUT field F = S1720Field, S1751's external input refutes
the literal full-action statement.  This is the concrete-field form of
S1752ActionForget_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing. -/
theorem S1752S1720_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing
    (h : S1751S1720NonOpenSubgroupMissing) :
    ¬ PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget S1720Field) (S1752G S1720Field) :=
  S1752ActionForget_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing
    S1720Field h

/-- Conditional EtaleFundamentalGroup from S1751's group-theoretic target. -/
noncomputable def S1752ActionEtaleFundamentalGroup_of_S1751Target
    (F : Type) [Field F] (h : S1751Target F) :
    Iut.EtaleFundamentalGroup :=
  S1752ActionEtaleFundamentalGroup_of_everyFiniteIndexOpen F h

/-- The EtaleFundamentalGroup certifies the literal fundamental-group
statement, read back from its stored field. -/
theorem S1752ActionEtaleFundamentalGroup_certified
    (F : Type) [Field F] (h : S1752ActionForgetMissing F) :
    letI := (S1752ActionEtaleFundamentalGroup F h).coverCategory
    letI := (S1752ActionEtaleFundamentalGroup F h).galoisCategory
    letI := (S1752ActionEtaleFundamentalGroup F h).fiberFunctor
    letI (X : (S1752ActionEtaleFundamentalGroup F h).Cover) :=
      (S1752ActionEtaleFundamentalGroup F h).action X
    PreGaloisCategory.IsFundamentalGroup
      (S1752ActionEtaleFundamentalGroup F h).fiber
      (S1752ActionEtaleFundamentalGroup F h).group :=
  (S1752ActionEtaleFundamentalGroup F h).isFundamentalGroup

/-! ## 6. Unconditional cases of the missing condition -/

/-- A subsingleton topological group has only continuous finite actions: the
scalar map is the second projection. -/
theorem S1752AllFiniteActionsContinuous_of_subsingleton
    (G : Type) [Group G] [TopologicalSpace G] [Subsingleton G] :
    S1737AllFiniteActionsContinuous G := by
  intro X
  change ContinuousSMul G X.V
  constructor
  have h : (fun p : G × X.V => p.1 • p.2) = fun p => p.2 := by
    funext p
    rw [Subsingleton.elim p.1 1, one_smul]
  rw [h]
  exact continuous_snd

/-- For a separably closed field the absolute Galois group is trivial. -/
theorem S1752AbsoluteGalois_subsingleton_of_isSepClosed
    (F : Type) [Field F] [IsSepClosed F] :
    Subsingleton (S1752G F) := by
  show Subsingleton (SeparableClosure F ≃ₐ[F] SeparableClosure F)
  constructor
  intro f g
  ext x
  have hbot : separableClosure F (AlgebraicClosure F) = ⊥ :=
    (IsSepClosed.separableClosure_eq_bot_iff F (AlgebraicClosure F)).mpr
      inferInstance
  have hx : (x : AlgebraicClosure F) ∈
      (⊥ : IntermediateField F (AlgebraicClosure F)) := by
    rw [← hbot]
    exact x.2
  obtain ⟨a, ha⟩ := (IntermediateField.mem_bot).mp hx
  have hx' : x = algebraMap F (SeparableClosure F) a := by
    apply Subtype.ext
    exact ha.symm
  rw [hx', AlgEquiv.commutes, AlgEquiv.commutes]

/-- The missing condition is discharged for separably closed fields. -/
theorem S1752ActionForgetMissing_of_isSepClosed
    (F : Type) [Field F] [IsSepClosed F] :
    S1752ActionForgetMissing F := by
  haveI : Subsingleton (S1752G F) :=
    S1752AbsoluteGalois_subsingleton_of_isSepClosed F
  exact S1752AllFiniteActionsContinuous_of_subsingleton (S1752G F)

/-- **Unconditional literal target for separably closed F.** -/
theorem S1752ActionForget_isFundamentalGroup_of_isSepClosed
    (F : Type) [Field F] [IsSepClosed F] :
    PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) :=
  S1752ActionForget_isFundamentalGroup F
    (S1752ActionForgetMissing_of_isSepClosed F)

/-- **Unconditional EtaleFundamentalGroup for separably closed F.** -/
noncomputable def S1752ActionEtaleFundamentalGroup_of_isSepClosed
    (F : Type) [Field F] [IsSepClosed F] :
    Iut.EtaleFundamentalGroup :=
  S1752ActionEtaleFundamentalGroup F
    (S1752ActionForgetMissing_of_isSepClosed F)

/-- The finite-group case of S1737 also discharges the missing condition: a
finite topological group is discrete, so all its finite actions are
continuous. -/
theorem S1752ActionForgetMissing_of_finite
    (F : Type) [Field F] [Finite (S1752G F)] :
    S1752ActionForgetMissing F :=
  S1737AllFiniteActionsContinuous_of_finite (S1752G F)

/-- **Unconditional literal target when the absolute Galois group is finite.** -/
theorem S1752ActionForget_isFundamentalGroup_of_finite
    (F : Type) [Field F] [Finite (S1752G F)] :
    PreGaloisCategory.IsFundamentalGroup
      (S1752ActionForget F) (S1752G F) :=
  S1752ActionForget_isFundamentalGroup F
    (S1752ActionForgetMissing_of_finite F)

/-- **Unconditional EtaleFundamentalGroup when the absolute Galois group is
finite.** -/
noncomputable def S1752ActionEtaleFundamentalGroup_of_finite
    (F : Type) [Field F] [Finite (S1752G F)] :
    Iut.EtaleFundamentalGroup :=
  S1752ActionEtaleFundamentalGroup F
    (S1752ActionForgetMissing_of_finite F)

/-! ## 7. Axiom footprint -/

#check S1752G
#check S1752ActionForgetMissing
#check S1752ActionForgetMissing_iff_everyFiniteIndexOpen
#check S1752ActionForget_isFundamentalGroup
#check S1752ActionForget_isFundamentalGroup_iff_missing
#check S1752ActionForgetToAutContinuous
#check S1752ActionForgetMissing_iff_exists_continuousMulEquiv
#check S1752ActionEtaleFundamentalGroup
#check S1752ActionEtaleFundamentalGroup_certified
#check S1752ActionForgetMissing_of_isSepClosed
#check S1752ActionEtaleFundamentalGroup_of_isSepClosed
#check S1752ActionForgetMissing_of_finite
#check S1752ActionForget_isFundamentalGroup_of_everyFiniteIndexOpen
#check S1752ActionForget_isFundamentalGroup_of_S1751Target
#check S1752ActionForget_isFundamentalGroup_of_continuousMulEquiv
#check S1737ActionForget_isFundamentalGroup
#check S1752ActionForget_not_isFundamentalGroup_of_not_missing
#check S1752ActionForget_not_isFundamentalGroup_of_nonOpen
#check S1752ActionEtaleFundamentalGroup_of_everyFiniteIndexOpen
#check S1752ActionEtaleFundamentalGroup_of_continuousMulEquiv
#check S1752ActionForgetMissing_iff_S1751Target
#check S1752ActionForgetMissing_false_iff_S1751Refutation
#check S1752ActionForgetMissing_false_of_S1751NonOpenSubgroupMissing
#check S1752ActionForget_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing
#check S1752ActionEtaleFundamentalGroup_of_S1751Target
#check S1752S1720_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing
#check S1752ActionGaloisCategoryData.of

#print axioms S1752ActionGaloisCategoryCertificate.of
#print axioms S1752ActionGaloisCategoryData.of
#print axioms S1752ActionAutCertificate
#print axioms S1752ActionForgetMissing_iff_everyFiniteIndexOpen
#print axioms S1752ActionForget_isFundamentalGroup
#print axioms S1752ActionForget_isFundamentalGroup_iff_missing
#print axioms S1752ActionForgetToAutContinuous
#print axioms S1752ActionForgetToAutContinuous_smul
#print axioms S1752ActionForgetMissing_iff_exists_continuousMulEquiv
#print axioms S1752ActionEtaleFundamentalGroup
#print axioms S1752ActionEtaleFundamentalGroup_certified
#print axioms S1752AllFiniteActionsContinuous_of_subsingleton
#print axioms S1752AbsoluteGalois_subsingleton_of_isSepClosed
#print axioms S1752ActionForgetMissing_of_isSepClosed
#print axioms S1752ActionForget_isFundamentalGroup_of_isSepClosed
#print axioms S1752ActionEtaleFundamentalGroup_of_isSepClosed
#print axioms S1752ActionForget_isFundamentalGroup_of_everyFiniteIndexOpen
#print axioms S1752ActionForget_isFundamentalGroup_of_S1751Target
#print axioms S1752ActionForget_isFundamentalGroup_of_continuousMulEquiv
#print axioms S1737ActionForget_isFundamentalGroup
#print axioms S1752ActionForget_not_isFundamentalGroup_of_not_missing
#print axioms S1752ActionForget_not_isFundamentalGroup_of_nonOpen
#print axioms S1752ActionEtaleFundamentalGroup_of_everyFiniteIndexOpen
#print axioms S1752ActionEtaleFundamentalGroup_of_continuousMulEquiv
#print axioms S1752ActionForgetMissing_iff_S1751Target
#print axioms S1752ActionForgetMissing_false_iff_S1751Refutation
#print axioms S1752ActionForgetMissing_false_of_S1751NonOpenSubgroupMissing
#print axioms S1752ActionForget_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing
#print axioms S1752ActionEtaleFundamentalGroup_of_S1751Target
#print axioms S1752S1720_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing
#print axioms S1752ActionForgetMissing_of_finite
#print axioms S1752ActionEtaleFundamentalGroup_of_finite

end LeanFormal.IUT.XiFPaper.S1752ActionFundamentalActual
