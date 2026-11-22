import tmp.sheaf.xif.paper.S462Example32PhiIsoGroupLikeActual
import tmp.sheaf.xif.paper.S451GroupLikePullbackAuditActual

/-! # S486: ULift GroupLikeAddMonoidOn for Example32 rational functions -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S486Example32ULiftGroupLikeActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S462Example32PhiIsoGroupLikeActual
open LeanFormal.IUT.XiFPaper.S451GroupLikePullbackAuditActual
open Iut.SourceModelFrobenioid

universe u

variable (K : Type u) [Field K]

/-- ULift of rational-function units, at the universe required by the base. -/
abbrev Example32ULiftUnits (X : Example32SmallBase K) : Type (u + 1) :=
  ULift.{u + 1} (Example32CoverField K X)ˣ

/-- Lifted inclusion pullback. -/
noncomputable def example32ULiftPullback
    {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    Additive (Example32ULiftUnits K Y) →+
      Additive (Example32ULiftUnits K X) where
  toFun z :=
    Additive.ofMul (ULift.up (Additive.toMul
      (example32RationalPullback (K := K) f
        (Additive.ofMul z.toMul.down))))
  map_zero' := by
    apply Additive.toMul.injective
    ext
    simp
  map_add' x y := by
    apply Additive.toMul.injective
    ext
    simp [map_add]

end LeanFormal.IUT.XiFPaper.S486Example32ULiftGroupLikeActual

end
