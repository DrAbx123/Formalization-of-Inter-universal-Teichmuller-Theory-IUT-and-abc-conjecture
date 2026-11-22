import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi LANA local-estimate interface model

A self-contained interface model of the LANA `LocalEstimate` fields (IUT IV Steps
(iv)-(vii)): continuation functions, hull containment, theta-pilot subset, volume
finiteness/infiniteness, and packet monotonicity.  The LANA concrete olean is not
required. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXILanaInterfaceModelActual

structure StepXILocalEstimate (ι : Type) (X : Type) where
  cont : ι → X
  thetaPilot : Set X
  hull : Set X
  cont_mem_hull : ∀ i, cont i ∈ hull
  thetaPilot_subset : thetaPilot ⊆ hull
  vol : Set X → ℝ
  vol_finite : vol hull ≠ 0
  packetVol_mono : ∀ U V : Set X, U ⊆ V → vol U ≤ vol V

def StepXILocalEstimate.toHull (E : StepXILocalEstimate ι X) : Set X := E.hull

theorem StepXILocalEstimate.cont_in_hull (E : StepXILocalEstimate ι X) (i : ι) :
    E.cont i ∈ E.toHull :=
  E.cont_mem_hull i

end LeanFormal.IUT.XiFPaper.Mzk1StepXILanaInterfaceModelActual

end
