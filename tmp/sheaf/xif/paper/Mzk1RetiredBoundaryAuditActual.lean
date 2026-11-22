import tmp.sheaf.xif.paper.Mzk1Stage4A703CorrectionActual

/-! # Mzk1RetiredBoundaryAuditActual (stage4 lane; A704 retired-boundary audit)

**A704 (user audit)**: the following boundary results are RETRACTED (kept as history,
never deleted, never cited as conclusions):
* `final_conditional_ABC` — its `hfull` hypothesis is UNSATISFIABLE for fixed `T`
  (machine-proved in `Mzk1Stage4A703CorrectionActual.hfull_unsatisfiable`), so the
  theorem is VACUOUS;
* `natRadicalWeightBound_iff_ABC` — VACUOUS for the same reason;
* `final_theorem_package` — not usable as a conclusion;
* the `N = a+b+c+1` scaling — NOT the paper structure (paper bad primes are the prime
  factors of `abc`).

The 3.12 chain is NOT load-bearing (e.g. `thetaReading` has no upper bound).  New work
must use triple-dependent Theta-data (N1: `q = (abc)^2`, bad primes = primes(abc)) with
the normalized weight `Σ_{p|abc} log p` (i.e. `[F_v:Q_p]/[F:Q]` normalization).
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1RetiredBoundaryAuditActual

/-- One retired-boundary row. -/
structure RetiredRow where
  /-- the retired result/tool. -/
  item : String
  /-- why it is retired. -/
  reason : String
  /-- what replaces it. -/
  replacement : String
  deriving Repr, DecidableEq

/-- The A704 retired-boundary inventory (stage4 lane). -/
def retiredRows : List RetiredRow :=
  [ ⟨"final_conditional_ABC", "hfull unsatisfiable for fixed T (machine-proved); theorem VACUOUS", "triple-dependent Theta-data route (N1)"⟩
  , ⟨"natRadicalWeightBound_iff_ABC", "vacuous by the same hfull unsatisfiability", "pure arithmetic BadSumWeightBound, independently stated"⟩
  , ⟨"final_theorem_package", "contains the vacuous conditional; not a conclusion", "explicit-hypothesis statement only"⟩
  , ⟨"N = a+b+c+1 scaling", "not the paper structure: paper bad primes = primes of abc", "N1: q=(abc)^2, bad primes = primes(abc)"⟩
  , ⟨"unnormalized local degrees", "coefficient obstruction without normalization", "normalized weight sum_p log p with [F_v:Q_p]/[F:Q]"⟩
  , ⟨"3.12 chain as load-bearing", "thetaReading has no upper bound; chain does not bear weight", "explicit named hypotheses, no closure claim"⟩
  ]

/-- The retired inventory has six rows. -/
theorem retiredRows_length : retiredRows.length = 6 := rfl

/-- A704 directive rows for new stage4 work. -/
def newRouteRows : List (String × String) :=
  [ ("Theta-data", "triple-dependent; N1: q = (abc)^2 (v_p(q) = 2 v_p(abc))")
    , ("bad primes", "exactly the prime factors of abc")
    , ("weight", "normalizedWeight = Σ_{p|abc} log p (after [F_v:Q_p]/[F:Q] normalization)")
    , ("retired tools", "final_conditional_ABC, natRadicalWeightBound_iff_ABC, final_theorem_package, N-scaling: NOT cited")
  ]

/-- The new-route record has four rows. -/
theorem newRouteRows_length : newRouteRows.length = 4 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4A703CorrectionActual.hfull_unsatisfiable
#check retiredRows_length
#check newRouteRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RetiredBoundaryAuditActual
end
