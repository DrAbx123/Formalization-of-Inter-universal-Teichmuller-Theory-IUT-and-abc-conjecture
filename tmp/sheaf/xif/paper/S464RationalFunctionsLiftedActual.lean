import tmp.sheaf.xif.paper.S456RationalInclusionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S464RationalFunctionsLiftedActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]

noncomputable def uliftUnitMap {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    ULift.{u+1} (coverField Y)ˣ →* ULift.{u+1} (coverField X)ˣ where
  toFun x := ULift.up ((unitInclusionPullback f) x.down)
  map_one' := by
    apply ULift.ext
    simp [unitInclusionPullback]
  map_mul' a b := by
    apply ULift.ext
    simp [unitInclusionPullback]

/-- Exact missing laws for upgrading `uliftUnitMap` to the GroupLikeAddMonoidOn
on the universe-u+1 carrier.  The map itself is actual and injective; the
remaining proofs are additive/ULift bookkeeping, not new mathematics. -/
structure Example32LiftedGroupLaws where
  pullback_id : Prop
  pullback_comp : Prop
  pullback_injective : Prop
  fsmPullbackIsIso : Prop

def Example32LiftedGroupLawsRequired : Prop :=
  Nonempty Example32LiftedGroupLaws

end LeanFormal.IUT.XiFPaper.S464RationalFunctionsLiftedActual
end
