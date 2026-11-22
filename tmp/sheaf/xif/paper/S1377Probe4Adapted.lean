import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
#check xCoordinateFormula_step
#check @xCoordinateFormula_step
#check Int.natAbs_of_nonneg
#check Int.natAbs_pos
#check Int.one_le_natAbs
#check Int.natAbs_eq
#check Int.ofNat_natAbs
#check Int.natAbs_eq_iff
example {n : ℤ} (h : 1 ≤ n) : 1 ≤ n.natAbs := by omega
