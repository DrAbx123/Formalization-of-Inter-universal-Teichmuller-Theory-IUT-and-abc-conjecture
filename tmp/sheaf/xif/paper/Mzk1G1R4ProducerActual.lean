import tmp.sheaf.xif.paper.Mzk1G1R4ProtectedActual

/-!
# R4.1 producer surface

This file exports the R4.1 producer surface built in Mzk1G1R4ProtectedActual.

Expected underlying names (documented by the R4 layer):
  * `protectedPointData_exists (S T)`          -- producer of the protected point data;
  * `protectedPointData_size_exists` / `_deg`  -- size existence form (deg D >= 2g+1);
  * `exists_s1_nonzero_on_of_h1`               -- choice of s1 by H1 vanishing;
  * `fiberAboveZero (psi : F)`                 -- the noncritical map datum (psi);
  * `ProtectedPointData.psi_structure`         -- bundled psi properties: psi_inv_zero,
                                                  zero_not_branch, zero_notin_psi_S;
  * `r4Rows` / `r4Rows_length`                 -- the 19-row target inventory.

The #check lines below pin the surface: when this file compiles, the exact names are the ones
printed here and can be quoted by consumers.
-/

noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual

namespace LeanFormal.IUT.XiFPaper.Mzk1G1R4ProducerActual

-- producer surface
#check @LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.protectedPointData_exists
#check @LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.protectedPointData_size_exists
#check @LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.protectedPointData_size_exists_deg
#check @LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.exists_s1_nonzero_on_of_h1
#check @LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.fiberAboveZero
#check @LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.psi_ratio_cover
#check @LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.r4Rows
#check @LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.r4Rows_length

-- psi_structure fields (pinned for consumers; the R4 layer bundles them in
-- ProtectedPointData.psi_structure)
#check @LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.ProtectedPointData.psi_structure
#check @LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.ProtectedPointData.psi_inv_zero
#check @LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.ProtectedPointData.zero_notin_psi_S
#check @LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.ProtectedPointData.zero_not_branch

-- the 19-row inventory, re-exported
def r4RowsExport : List (String × String × String) :=
  LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.r4Rows

theorem r4RowsExport_length : r4RowsExport.length = 19 :=
  LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.r4Rows_length

#print axioms r4RowsExport_length
end LeanFormal.IUT.XiFPaper.Mzk1G1R4ProducerActual