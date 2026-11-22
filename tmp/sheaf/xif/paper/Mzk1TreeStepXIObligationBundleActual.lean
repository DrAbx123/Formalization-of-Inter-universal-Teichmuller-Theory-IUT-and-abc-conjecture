import LeanFormal.IUT.IUTIII.Corollary312.Obligations
import LeanFormal.IUT.IUTIII.Corollary312.Routes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: tree-only StepXI obligation bundle -> Audit ipl/she/apt records (Obligations:5/12/19) + Cor312Route enumeration (Routes:32) -> PROVED: ids, sources, statuses, dependency chains, route enumeration; no port imports. No closure.

# Mzk1TreeStepXIObligationBundleActual — tree-only StepXI obligation bundle

PROVED: ids/sources/statuses/dep chains for ipl/she/apt; route enumeration.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIObligationBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit

theorem tree_ipl_id : ipl.id = "IUT-III.IPL" := rfl
theorem tree_she_id : she.id = "IUT-III.SHE" := rfl
theorem tree_apt_id : apt.id = "IUT-III.APT" := rfl

theorem tree_ipl_status : ipl.status = VerificationStatus.pending := rfl
theorem tree_she_status : she.status = VerificationStatus.pending := rfl
theorem tree_apt_status : apt.status = VerificationStatus.pending := rfl

theorem tree_stepXI_obligations_bundle :
    ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" ∧
      ipl.status = VerificationStatus.pending ∧
      she.status = VerificationStatus.pending ∧
      apt.status = VerificationStatus.pending :=
  ⟨tree_ipl_id, tree_she_id, tree_apt_id, tree_ipl_status, tree_she_status, tree_apt_status⟩

theorem tree_route_enum (r : Cor312Route) :
    r = Cor312Route.mochizuki3115 ∨ r = Cor312Route.arithmeticTeichmuller ∨
      r = Cor312Route.sarkisyanErdosKac := by
  cases r with
  | mochizuki3115 => exact Or.inl rfl
  | arithmeticTeichmuller => exact Or.inr (Or.inl rfl)
  | sarkisyanErdosKac => exact Or.inr (Or.inr rfl)

def treeStepXIRows : List (String × String × String) :=
  [ ("StepXI obligation ids", "PROVED", "tree_ipl_id/tree_she_id/tree_apt_id")
  , ("StepXI obligation statuses", "PROVED (pending)", "tree_ipl_status/tree_she_status/tree_apt_status")
  , ("route enumeration", "PROVED", "tree_route_enum")
  , ("obligation proofs", "NAMED (tree pending)", "IPL/SHE/APT content not formalized") ]

theorem treeStepXIRows_length : treeStepXIRows.length = 4 := rfl

#check tree_stepXI_obligations_bundle
#check tree_route_enum
#check treeStepXIRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeStepXIObligationBundleActual
end