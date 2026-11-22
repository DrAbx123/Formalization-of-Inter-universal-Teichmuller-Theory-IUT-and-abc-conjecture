import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-!
  Owned audit probe for the logarithmic-bound equivalence package
  (worker `dsh_log_bound`, run entry direct-abc-20261015, turn 2).

  It records the public signatures reached by the consumer, the checked
  alias identification `Statement.radical = natRadical`, and the transitive
  axiom closure of every new/changed declaration plus the named sibling
  dependencies.  No sibling source is read.
-/

-- Checked alias identification: same constant, for every n, by rfl.
example (n : Nat) : LeanFormal.IUT.radical n = LeanFormal.IUT.natRadical n := rfl

-- Public signatures of the new declarations.
#check @LeanFormal.IUT.radical_eq_natRadical
#check @LeanFormal.IUT.radical_log_eq_arithmeticWeight
#check @LeanFormal.IUT.abcConjecture_iff_abcArithmeticWeightHeightBound

-- Named public objects/dependencies of the terminal sibling.
#check @LeanFormal.IUT.arithmeticPrimeSupport
#check @LeanFormal.IUT.arithmeticWeight
#check @LeanFormal.IUT.arithmeticWeight_abcRationalPoint

-- Transitive axiom reports for new declarations.
#print axioms LeanFormal.IUT.radical_eq_natRadical
#print axioms LeanFormal.IUT.radical_log_eq_arithmeticWeight
#print axioms LeanFormal.IUT.abcConjecture_iff_abcArithmeticWeightHeightBound

-- Transitive axiom reports for the named sibling dependencies.
#print axioms LeanFormal.IUT.arithmeticPrimeSupport_abcRationalPoint
#print axioms LeanFormal.IUT.arithmeticWeight_abcRationalPoint
#print axioms LeanFormal.IUT.natRadical_cast_pos
#print axioms LeanFormal.IUT.natRadical_cast_log_eq_sum_primeFactors

-- Previous turn-1 declarations (mathematics unchanged).
#print axioms LeanFormal.IUT.logLeIffLeExpMulRpow
#print axioms LeanFormal.IUT.logLeIffLeMulRpow
#print axioms LeanFormal.IUT.abcLogBound_exists_iff_rpow_exists
#print axioms LeanFormal.IUT.abcLogHeightBound_exists_iff_rpow_exists
#print axioms LeanFormal.IUT.abcConjecture_iff_abcLogConjecture
