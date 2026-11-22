import tmp.sheaf.xif.paper.Mzk1RRInterfaceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1RRNegativeDegreeV2ActualAdapted (adapted copy, A475 reuse) — negative-degree RR consumer (fresh path)

DAG node: foundation:D.RRnegativeDegree.  The original consumer file fails at the
IsAlgClosed instance in the bundled place-degree statement; this fresh file provides
the unconditional negative-degree vanishing theorem from the interface only.
No closure claim; GATE NOT PASSED; registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1RRNegativeDegreeV2ActualAdapted

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1RRInterfaceActual

theorem rr_neg_ell_zero_v2 {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] {D : Divisor K F} (hD : Divisor.degree D < 0) :
    ell D = 0 := ell_eq_zero_of_degree_neg_interface hD

/-- Rows: negative-degree consumer status. -/
def rrNegV2Rows : List (String × String × String) :=
  [ ("negative-degree ell vanishing", "rr_neg_ell_zero_v2", "PROVED"),
    ("place-degree bundle", "omitted (original IsAlgClosed instance failure)", "DEFERRED"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem rrNegV2Rows_length : rrNegV2Rows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1RRNegativeDegreeV2ActualAdapted

end
