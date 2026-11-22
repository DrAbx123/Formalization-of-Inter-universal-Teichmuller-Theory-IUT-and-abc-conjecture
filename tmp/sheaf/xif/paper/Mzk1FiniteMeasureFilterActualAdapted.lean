import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActualAdapted

/-! # Mzk1FiniteMeasureFilterActualAdapted — filter bound for the finite measure (real)

Real Lean (no sorry/axiom): filtering a finite set cannot increase its maximal degree.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureFilterActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActualAdapted

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_filter_le (S : Finset Qbar) (p : Qbar -> Bool) :
    maxDeg (S.filter p) <= maxDeg S :=
  maxDeg_mono (Finset.filter_subset _ _)

theorem maxDeg_attach_le (S : Finset Qbar) :
    maxDeg (S.attach.image (fun x => x.1)) <= maxDeg S := by
  rw [Finset.image_attach]
  exact le_rfl

def finiteMeasureFilterRows : List (String × String) :=
  [ ("maxDeg_filter_le", "PROVED"), ("maxDeg_attach_le", "PROVED") ]

theorem finiteMeasureFilterRows_length : finiteMeasureFilterRows.length = 2 := rfl

#check maxDeg_filter_le

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureFilterActualAdapted
end
