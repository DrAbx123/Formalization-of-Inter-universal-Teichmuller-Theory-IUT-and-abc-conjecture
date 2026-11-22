import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # iutiv-abc:G0.log consumer audit; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1G0LogConsumerActual

open LeanFormal.IUT

#check logLeIffLeExpMulRpow
#check logLeIffLeMulRpow
#check ABCLogBound
#check ABCLogConjecture
#check abcTriple_c_pos
#check radical_log_eq_arithmeticWeight
#check abcLogBound_exists_iff_rpow_exists
#check abcLogHeightBound_exists_iff_rpow_exists

def g0LogConsumerRows : List (String × String × String) :=
  [ ("log<->exponential equivalence", "CONSUMED", "logLeIffLeExpMulRpow / logLeIffLeMulRpow"),
    ("ABC log bound/conjecture shapes", "DEFINED", "ABCLogBound / ABCLogConjecture"),
    ("radical/log dictionary", "CONSUMED", "radical_log_eq_arithmeticWeight"),
    ("log/rpow bound equivalence", "CONSUMED", "abcLogBound_exists_iff_rpow_exists / abcLogHeightBound_exists_iff_rpow_exists"),
    ("paper-level log equivalence", "NAMED", "no proof of ABC here; G0 target remains open") ]

theorem g0LogConsumerRows_length : g0LogConsumerRows.length = 5 := rfl

#check g0LogConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1G0LogConsumerActual
end