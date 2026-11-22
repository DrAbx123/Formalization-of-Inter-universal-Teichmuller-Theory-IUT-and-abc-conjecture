import tmp.sheaf.xif.paper.S486Example32ULiftGroupLikeActual
import tmp.sheaf.xif.paper.S474Example32GroupLikeIsoActual

/-! # S510: complete ULift GroupLikeAddMonoidOn from S469/S474

S469/S474 already construct the actual ULift rational-function group-like object
with IsFSM = IsIso.  S486 has the same carrier and lifted pullback.  This file
records the equality of the S486 lifted pullback with the S469 one and
re-exports the complete actual GroupLikeAddMonoidOn. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S510Example32ULiftGroupLikeCompleteActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S469RationalFunctionsLiftedActual
open LeanFormal.IUT.XiFPaper.S474Example32GroupLikeIsoActual
open LeanFormal.IUT.XiFPaper.S486Example32ULiftGroupLikeActual
open Iut.SourceModelFrobenioid

universe u
variable (K : Type u) [Field K]

/-- Complete actual GroupLikeAddMonoidOn with IsFSM = IsIso. -/
noncomputable def s510GroupLike :
    GroupLikeAddMonoidOn (Example32SmallBase K) (Example32FSMIso (K := K)) :=
  example32RationalFunctionsIso (K := K)

/-- The complete object has the actual ULift unit carrier. -/
theorem s510GroupLike_obj (X : Example32SmallBase K) :
    (s510GroupLike (K := K)).obj X =
      Additive (ULift.{u+1} (coverField X)ˣ) := rfl

end LeanFormal.IUT.XiFPaper.S510Example32ULiftGroupLikeCompleteActual

end
