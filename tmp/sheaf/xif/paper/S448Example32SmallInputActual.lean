import tmp.sheaf.xif.paper.S432SmallModelActual
import tmp.sheaf.xif.paper.S433Example32RationalDivisorActual
import tmp.sheaf.xif.paper.S442DvCoverNormPullbackActual
import tmp.sheaf.xif.paper.S446Example32DivisorNaturalityActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S448Example32SmallInputActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S433Example32RationalDivisorActual
open LeanFormal.IUT.XiFPaper.S442DvCoverNormPullbackActual
open LeanFormal.IUT.XiFPaper.S446Example32DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual
open Iut.SourceModelFrobenioid

universe u
variable (K : Type u) [Field K]

/-- Actual rational-function object family: Additive (L_X)^×. -/
abbrev Example32SmallRationalObject (X : Example32SmallBase K) : Type u :=
  Additive (X.unop.obj.obj)ˣ

/-- Exact missing norm bridge from the size-aligned base to algebra maps.
The opposite/ULift direction is not supplied by S442/S446, which live on the
covariant DvTriangleFieldCover category. -/
structure Example32SmallNormBridge where
  toAlgHom : ∀ {X Y : Example32SmallBase K},
    (X ⟶ Y) → X.unop.obj.obj →ₐ[K] Y.unop.obj.obj
  direction_ok : Prop
  norm_pullback_law : Prop
  norm_id_law : Prop
  norm_comp_law : Prop

/-- Exact missing data to fill the S432 Input. -/
structure Example32SmallInputGap where
  bridge : Example32SmallNormBridge (K := K)
  valuationFamily : Prop
  normCompatibility : Prop
  divisorNaturality : Prop
  rationalFunctions_obj_eq : Prop
  pullback_norm_eq : Prop
  divisor_eq_coefficient : Prop

def Example32SmallInputRequired : Prop :=
  Nonempty (Example32SmallInputGap (K := K))

/-- The exact missing object fields, kept as a proposition (no inhabitant). -/
def MissingExample32SmallInputFields : Prop :=
  Example32SmallInputRequired (K := K)

end LeanFormal.IUT.XiFPaper.S448Example32SmallInputActual

end
