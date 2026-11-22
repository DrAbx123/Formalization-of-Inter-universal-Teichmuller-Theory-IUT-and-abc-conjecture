import tmp.sheaf.xif.paper.Mzk1FinalBoundaryCertificateV2Actual
import tmp.sheaf.xif.paper.Mzk1FinalBoundaryCertificateV2ShaActual
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual

/-! # FinalBoundaryV2 status table audit (read-only, lattice prefix)

A704 RETRACTION NOTICE: the old path based on `final_conditional_ABC`,
`natRadicalWeightBound_iff_ABC` and `N = a + b + c + 1` scaling is RETRACTED:
the hypothesis `hfull` is unsatisfiable, so those statements are vacuous.
They are kept only as history.  New work uses triple-dependent Theta-data (N1):
bad primes = primes(abc), q = (abc)^2, normalized weight [F_v:Q_p]/[F:Q].
The old table rows below carry explicit RETRACTED marks. -/

def v2StatusRows : List (String × String) :=
  [ ("old Cor 3.12 / final_conditional_ABC path", "RETRACTED (3.12 chain NOT load-bearing)"),
    ("final_conditional_ABC", "RETRACTED / VACUOUS (hfull unsatisfiable)"),
    ("natRadicalWeightBound_iff_ABC", "RETRACTED / VACUOUS"),
    ("N = a + b + c + 1 three-way scaling", "RETRACTED (not the paper structure)"),
    ("N1: bad primes = primes(abc)", "NEW ROUTE (triple-dependent Theta-data)"),
    ("N1: q = (abc)^2 (v_p(q) = 2 v_p(abc))", "NEW ROUTE (concrete N1 model)"),
    ("N1: normalized weight [F_v:Q_p]/[F:Q]", "NEW ROUTE (normalized; no d_b obstacle)"),
    ("old corrected-region Gap2 shape", "NAMED (historical; replaced by N1 arithmetic target)") ]

theorem v2StatusRows_length : v2StatusRows.length = 8 := rfl

#check LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.finalBoundaryCertificateV2
#check LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.correctedGap2_iff_arith
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.finalBoundaryCertificateV2
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.correctedGap2_iff_arith
