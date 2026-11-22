import tmp.sheaf.xif.paper.Mzk1FiniteMeasureLawsActual

/-! # Mzk1FiniteMeasureConsumerActual — finite-measure subset corollaries (real)

Real Lean (no sorry/axiom): erase/intersection bounds for the finite-part measure derived
from the PROVED monotonicity law.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureLawsActual

attribute [local instance] Classical.decEq

universe u

theorem maxDeg_erase_le (S : Finset Qbar) (x : Qbar) :
    maxDeg (S.erase x) <= maxDeg S :=
  maxDeg_mono (Finset.erase_subset _ _)

theorem maxDeg_inter_le (S T : Finset Qbar) : maxDeg (S ∩ T) <= maxDeg S :=
  maxDeg_mono (Finset.inter_subset_left _ _)

theorem maxDeg_diff_le (S T : Finset Qbar) : maxDeg (S \ T) <= maxDeg S :=
  maxDeg_mono (Finset.diff_subset _ _)

def finiteMeasureConsumerRows : List (String × String) :=
  [ ("maxDeg_erase_le", "PROVED"), ("maxDeg_inter_le", "PROVED"),
    ("maxDeg_diff_le", "PROVED") ]

theorem finiteMeasureConsumerRows_length : finiteMeasureConsumerRows.length = 3 := rfl

#check maxDeg_erase_le

end LeanFormal.IUT.XiFPaper.Mzk1FiniteMeasureConsumerActual
end
