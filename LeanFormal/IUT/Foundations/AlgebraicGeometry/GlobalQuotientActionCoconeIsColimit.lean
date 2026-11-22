import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Action cocone universal property and gluing-diagram reduction

This file proves the universal property of the action cocone attached to
`GlobalActionCoconeData`, and reduces its colimit statement to a gluing-diagram
colimit plus a cocone isomorphism.  The only genuine `G`-equivariance input is
the invariant projection `proj_invariant`; no colimit is fabricated.
-/
namespace ABCBridge.GlobalQuotientActionCoconeIsColimit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionData

universe u

variable {R : Type u} [CommRing R]
variable {S : Scheme.{u}} {G : Type u} [Group G] [Finite G]
  {F : SingleObj G ⥤ FiniteEtaleCover S}

/-- The genuine `G`-equivariance of the projection, restated as a stand-alone
condition. -/
def GenuineGEquivariance (D : GlobalActionCoconeData S G F) : Prop :=
  ∀ g : G, F.map g ≫ D.proj = D.proj

/-- The universal property of the action cocone: every cocone over the action
diagram factors uniquely through the action cocone. -/
def CoconeUniversal (D : GlobalActionCoconeData S G F) : Prop :=
  ∀ c : Cocone F,
    ∃! u : D.quotient ⟶ c.pt,
      ∀ j : SingleObj G, D.cocone.ι.app j ≫ u = c.ι.app j

/-- The action cocone universal property is equivalent to being a colimit. -/
theorem coconeUniversal_iff_isColimit
    (D : GlobalActionCoconeData S G F) :
    CoconeUniversal D ↔ Nonempty (IsColimit D.cocone) := by
  constructor
  · intro h
    refine ⟨IsColimit.mk (fun c => (h c).choose)
      (fun c j => (h c).choose_spec.1 j) ?_⟩
    intro c u hu
    exact (h c).choose_spec.2 u hu
  · rintro ⟨I⟩ c
    exact ⟨I.desc c, I.fac c, fun u hu => I.uniq c u hu⟩

/-- The invariant projection supplies the genuine equivariance needed by the
cocone. -/
theorem genuineGEquivariance_of_invariant
    (D : GlobalActionCoconeData S G F) :
    GenuineGEquivariance D :=
  D.proj_invariant

/-- Transfer a gluing-diagram colimit to the actual action cocone, given an
isomorphism of cocones.  This is the exact reduction to the gluing diagram. -/
theorem isColimit_of_gluingCocone
    (D : GlobalActionCoconeData S G F)
    (Gc : Cocone F) (hGc : IsColimit Gc)
    (e : D.cocone ≅ Gc) :
    IsColimit D.cocone :=
  IsColimit.ofIsoColimit hGc e.symm

/-- The gluing-diagram reduction receives the action cocone universal property. -/
theorem coconeUniversal_of_gluingCocone
    (D : GlobalActionCoconeData S G F)
    (Gc : Cocone F) (hGc : IsColimit Gc)
    (e : D.cocone ≅ Gc) :
    CoconeUniversal D :=
  (coconeUniversal_iff_isColimit D).mpr
    ⟨isColimit_of_gluingCocone D Gc hGc e⟩

/-- A gluing-diagram comparison package: the gluing cocone, its colimit proof,
and the action-cocone isomorphism.  This is explicit input, not a manufactured
colimit. -/
structure GluingActionCoconeComparison
    (D : GlobalActionCoconeData S G F) where
  glueCocone : Cocone F
  glueIsColimit : IsColimit glueCocone
  actionIso : D.cocone ≅ glueCocone

/-- The gluing comparison yields the action cocone colimit. -/
theorem isColimit_of_gluingComparison
    (D : GlobalActionCoconeData S G F)
    (C : GluingActionCoconeComparison D) :
    IsColimit D.cocone :=
  isColimit_of_gluingCocone D C.glueCocone C.glueIsColimit C.actionIso

/-- The gluing comparison yields the action cocone universal property. -/
theorem coconeUniversal_of_gluingComparison
    (D : GlobalActionCoconeData S G F)
    (C : GluingActionCoconeComparison D) :
    CoconeUniversal D :=
  coconeUniversal_of_gluingCocone D C.glueCocone C.glueIsColimit C.actionIso

/-- The action cocone data attached to an actual global quotient action data. -/
noncomputable def actionCoconeDataOfActionData
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (A : GlobalQuotientActionData (R := R) X G) :
    GlobalActionCoconeData (Spec (CommRingCat.of R)) G A.actionFunctor where
  quotient := A.quotientCover
  proj := A.projection
  proj_invariant := A.projection_invariant

/-- The attached action cocone data has the packaged quotient cover as point. -/
theorem actionCoconeDataOfActionData_quotient
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (A : GlobalQuotientActionData (R := R) X G) :
    (actionCoconeDataOfActionData (R := R) A).quotient = A.quotientCover :=
  rfl

/-- The attached projection is the packaged projection. -/
theorem actionCoconeDataOfActionData_proj
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (A : GlobalQuotientActionData (R := R) X G) :
    (actionCoconeDataOfActionData (R := R) A).proj = A.projection :=
  rfl

/-- The attached cocone is the packaged cocone. -/
theorem actionCoconeDataOfActionData_cocone
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (A : GlobalQuotientActionData (R := R) X G) :
    (actionCoconeDataOfActionData (R := R) A).cocone = A.cocone :=
  rfl

/-- The gluing reduction for the actual action data: once a gluing-diagram
colimit and a cocone isomorphism are supplied, the packaged projection cocone is
a colimit. -/
theorem actionCoconeData_isColimit_of_gluing
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (A : GlobalQuotientActionData (R := R) X G)
    (C : GluingActionCoconeComparison
      (actionCoconeDataOfActionData (R := R) A)) :
    IsColimit (actionCoconeDataOfActionData (R := R) A).cocone :=
  isColimit_of_gluingComparison
    (actionCoconeDataOfActionData (R := R) A) C

/-- The packaged action cocone universal property from the gluing comparison. -/
theorem actionData_coconeUniversal_of_gluing
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (A : GlobalQuotientActionData (R := R) X G)
    (C : GluingActionCoconeComparison
      (actionCoconeDataOfActionData (R := R) A)) :
    CoconeUniversal (actionCoconeDataOfActionData (R := R) A) :=
  coconeUniversal_of_gluingComparison
    (actionCoconeDataOfActionData (R := R) A) C


section UniversalProjections

/-- The universal property gives the existence part. -/
theorem coconeUniversal_desc
    (D : GlobalActionCoconeData S G F) (h : CoconeUniversal D)
    (c : Cocone F) :
    ∃ u : D.quotient ⟶ c.pt,
      ∀ j : SingleObj G, D.cocone.ι.app j ≫ u = c.ι.app j :=
  (h c).exists

/-- The universal property gives uniqueness. -/
theorem coconeUniversal_uniq
    (D : GlobalActionCoconeData S G F) (h : CoconeUniversal D)
    (c : Cocone F) (u : D.quotient ⟶ c.pt)
    (hu : ∀ j : SingleObj G, D.cocone.ι.app j ≫ u = c.ι.app j) :
    u = (h c).choose :=
  (h c).choose_spec.2 u hu

/-- A colimit cocone gives the universal property. -/
theorem coconeUniversal_of_isColimit
    (D : GlobalActionCoconeData S G F) (I : IsColimit D.cocone) :
    CoconeUniversal D :=
  (coconeUniversal_iff_isColimit D).mpr ⟨I⟩

/-- The universal property packages a colimit cocone. -/
theorem isColimit_of_coconeUniversal
    (D : GlobalActionCoconeData S G F) (h : CoconeUniversal D) :
    Nonempty (IsColimit D.cocone) :=
  (coconeUniversal_iff_isColimit D).mp h

/-- The genuine equivariance is exactly the projection-invariance condition. -/
theorem genuineGEquivariance_iff
    (D : GlobalActionCoconeData S G F) :
    GenuineGEquivariance D ↔ ∀ g : G, F.map g ≫ D.proj = D.proj :=
  Iff.rfl

/-- The invariant projection is the genuine equivariance input of the cocone. -/
theorem genuineGEquivariance_of_proj
    (D : GlobalActionCoconeData S G F) (g : G) :
    F.map g ≫ D.proj = D.proj :=
  D.proj_invariant g

/-- A cocone isomorphism transports the action cocone to any gluing cocone. -/
theorem gluingComparison_of_coconeIso
    (D : GlobalActionCoconeData S G F)
    (Gc : Cocone F) (hGc : IsColimit Gc)
    (e : D.cocone ≅ Gc) :
    GluingActionCoconeComparison D :=
  { glueCocone := Gc
    glueIsColimit := hGc
    actionIso := e }

/-- The action cocone universal property for the actual quotient action data,
from any gluing comparison. -/
theorem actionCoconeUniversal_of_gluing
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (A : GlobalQuotientActionData (R := R) X G)
    (C : GluingActionCoconeComparison
      (actionCoconeDataOfActionData (R := R) A)) :
    CoconeUniversal (actionCoconeDataOfActionData (R := R) A) :=
  coconeUniversal_of_gluingComparison
    (actionCoconeDataOfActionData (R := R) A) C

/-- The actual action cocone is a colimit from the gluing comparison. -/
theorem actionCoconeIsColimit_of_gluing
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (A : GlobalQuotientActionData (R := R) X G)
    (C : GluingActionCoconeComparison
      (actionCoconeDataOfActionData (R := R) A)) :
    IsColimit (actionCoconeDataOfActionData (R := R) A).cocone :=
  isColimit_of_gluingComparison
    (actionCoconeDataOfActionData (R := R) A) C

end UniversalProjections


section ComparisonProjections

/-- The gluing cocone carried by a gluing comparison. -/
theorem gluingComparison_glueCocone
    (D : GlobalActionCoconeData S G F) (C : GluingActionCoconeComparison D) :
    C.glueCocone = C.glueCocone :=
  rfl

/-- The gluing colimit proof carried by a gluing comparison. -/
theorem gluingComparison_glueIsColimit
    (D : GlobalActionCoconeData S G F) (C : GluingActionCoconeComparison D) :
    IsColimit C.glueCocone :=
  C.glueIsColimit

/-- The action-cocone isomorphism carried by a gluing comparison. -/
theorem gluingComparison_actionIso
    (D : GlobalActionCoconeData S G F) (C : GluingActionCoconeComparison D) :
    D.cocone ≅ C.glueCocone :=
  C.actionIso

/-- The attached action data inherits the genuine projection equivariance. -/
theorem actionCoconeDataOfActionData_genuine
    {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (A : GlobalQuotientActionData (R := R) X G) :
    GenuineGEquivariance (actionCoconeDataOfActionData (R := R) A) :=
  (actionCoconeDataOfActionData (R := R) A).proj_invariant

end ComparisonProjections

end ABCBridge.GlobalQuotientActionCoconeIsColimit
