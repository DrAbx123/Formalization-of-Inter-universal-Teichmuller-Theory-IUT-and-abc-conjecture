import tmp.sheaf.xif.paper.FlUnitsThetaPilotActionActual
import tmp.sheaf.xif.paper.IndeterminaciesActual

-- Actual F_l^x action vs source Theta-pilot action: compatibility/obstruction
--
-- The actual algebraic F_l^x action on SignedLabel is upgraded to an actual
-- permutation action (flUnitsEquivLabel / flUnitsActionPerm). The source
-- Theta-pilot action is the actual IndeterminaciesActual.labelPerm for a
-- supplied label permutation. The missing source homomorphism from F_l^x to
-- the label-permutation group (with its Kummer compatibility) is recorded as
-- an exact conditional input/obstruction, not fabricated.
-- WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionSourceActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionActual
open LeanFormal.IUT.XiFPaper.IndeterminaciesActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (v : V)

-- The actual algebraic F_l^x label action as a permutation.
noncomputable def flUnitsEquivLabel (u : (Fl l.value)ˣ) :
    Equiv.Perm (SignedLabel l.value) where
  toFun := flUnitsSmulLabel u
  invFun := flUnitsSmulLabel u⁻¹
  left_inv j := by
    unfold flUnitsSmulLabel
    rw [← mul_assoc, Units.val_inv_mul, one_mul, Equiv.symm_apply_apply]
  right_inv j := by
    unfold flUnitsSmulLabel
    rw [← mul_assoc, Units.val_mul_inv, one_mul, Equiv.symm_apply_apply]

-- The actual algebraic F_l^x permutation action.
noncomputable def flUnitsActionPerm :
    (Fl l.value)ˣ →* Equiv.Perm (SignedLabel l.value) where
  toFun := flUnitsEquivLabel
  map_one' := by
    ext j
    exact flUnitsSmulLabel_one j
  map_mul' u w := by
    ext j
    exact flUnitsSmulLabel_mul u w j

-- The actual source Theta-pilot action induced by a label permutation via the
-- actual IndeterminaciesActual.labelPerm.
noncomputable def sourceThetaPilotActionOfPerm
    (rho : (Fl l.value)ˣ →* Equiv.Perm (SignedLabel l.value)) :
    (Fl l.value)ˣ → I.ThetaPilotPoint v → I.ThetaPilotPoint v :=
  fun u => I.labelPerm v (rho u)

-- Exact missing source action: an actual homomorphism F_l^x -> label
-- permutations carrying the Kummer/source Theta-pilot action, together with
-- its compatibility with flUnitsActionPerm.
structure FlUnitsThetaPilotSourceActionData where
  sourceAction : (Fl l.value)ˣ →* Equiv.Perm (SignedLabel l.value)
  compat : Prop

def FlUnitsThetaPilotSourceActionObstruction : Prop :=
  Nonempty (FlUnitsThetaPilotSourceActionData (l := l))

-- Conditional actual compatibility object from an explicit source action hom
-- and its exact compatibility hypothesis.
noncomputable def flUnitsThetaPilotSourceActionOfHom
    (rho : (Fl l.value)ˣ →* Equiv.Perm (SignedLabel l.value))
    (hcompat : Prop) :
    FlUnitsThetaPilotSourceActionData (l := l) where
  sourceAction := rho
  compat := hcompat

-- The actual source Theta-pilot action built from flUnitsActionPerm itself is
-- the concrete action available from the algebraic side; it is not asserted to
-- be the paper's Kummer action.
noncomputable def algebraicSourceThetaPilotAction :
    (Fl l.value)ˣ → I.ThetaPilotPoint v → I.ThetaPilotPoint v :=
  sourceThetaPilotActionOfPerm (I := I) v (flUnitsActionPerm (l := l))

#check flUnitsEquivLabel
#check flUnitsActionPerm
#check sourceThetaPilotActionOfPerm
#check FlUnitsThetaPilotSourceActionData
#check FlUnitsThetaPilotSourceActionObstruction
#check flUnitsThetaPilotSourceActionOfHom
#check algebraicSourceThetaPilotAction

end LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionSourceActualAdapted

end