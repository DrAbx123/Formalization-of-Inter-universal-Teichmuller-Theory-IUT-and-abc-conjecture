import tmp.sheaf.xif.paper.Mzk1IutIVProp14iiiBoxFormalActual
/-! Legacy compatibility stub.

The old Iut-based path `Iut.Concrete.LocalConstruct.Prop14Lattice` is not part of the
current build closure (Iut/TFG files were removed from the watchdog WL).  The actual Box (11)
entry is now `Mzk1IutIVProp14iiiBoxFormalActual.prop14iii_box_formal`, proved from the
LeanFormal StepV tensor assembly.  This file intentionally keeps no Iut import.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14iiiBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14iiiBoxFormalActual
/-- Pointer to the actual Box (11) theorem now used instead of the old Iut wrapper. -/
def replacedByFormalBox : List String :=
  [ "Mzk1IutIVProp14iiiBoxFormalActual.prop14iii_box_formal" ]
theorem replacedByFormalBox_length : replacedByFormalBox.length = 1 := rfl
#check LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14iiiBoxFormalActual.prop14iii_box_formal
end LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14iiiBoxActual
end
