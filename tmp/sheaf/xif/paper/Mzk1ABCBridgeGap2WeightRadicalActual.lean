/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import Mathlib.Data.Real.Basic

/-! # A690: explicit natRadical form of the BadSumWeightBound weight -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap2WeightRadical

open LeanFormal.IUT

/-- **Explicit radical form**: on an ABC triple, the arithmetic weight of the rational
point `a/c` is `log rad(a*b*c)` (the project radical `natRadical`, cast to `ℝ`).
This is the exact identity behind the pure-arithmetic `BadSumWeightBound`; it does not
claim any converse estimate. -/
theorem arithmeticWeight_abc_eq_log_natRadical {a b c : Nat} (h : IsABCTriple a b c) :
    arithmeticWeight (abcRationalPoint a c) = Real.log ((natRadical (a * b * c) : Nat) : ℝ) := by
  rw [arithmeticWeight, arithmeticPrimeSupport_abcRationalPoint h,
    ← natRadical_cast_log_eq_sum_primeFactors]

/-- The same identity with the radical inside the log (convenience form). -/
theorem arithmeticWeight_abc_eq_log_radical' {a b c : Nat} (h : IsABCTriple a b c) :
    arithmeticWeight (abcRationalPoint a c) =
      Real.log ((natRadical (a * b * c) : Nat) : ℝ) := 
  arithmeticWeight_abc_eq_log_natRadical h

end LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap2WeightRadical
