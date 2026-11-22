import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
  Logarithmic-bound equivalence for the arithmetic ABC bridge.

  The estimates produced on the IUT side are additive in `Real.log` of the
  height, while the standard integer ABC statement is multiplicative in a
  radical power.  This file proves that the two shapes are equivalent for
  every real exponent (in particular `1 + epsilon` with any sign), with a
  positive multiplicative constant corresponding to an additive constant plus
  `Real.log` of that constant.

  The equivalence is proved from scratch via `Real.log_le_iff_le_exp` and
  `Real.rpow_def_of_pos`; no ABC estimate is assumed, and the existing
  `ABCInequality` definition is reused rather than restated.
-/

namespace LeanFormal.IUT

/--
Real logarithmic-to-`rpow` equivalence with an arbitrary additive constant.

For `h > 0` and `r > 0`, the additive inequality `log h <= t * log r + A`
is equivalent to the multiplicative inequality `h <= exp A * r ^ t`, for
every real exponent `t` (including `t <= 0`).
-/
theorem logLeIffLeExpMulRpow {h r A t : Real} (hh : 0 < h) (hr : 0 < r) :
    Real.log h ≤ t * Real.log r + A ↔ h ≤ Real.exp A * r ^ t := by
  have hpow : Real.exp (t * Real.log r + A) = Real.exp A * r ^ t := by
    rw [Real.exp_add, Real.rpow_def_of_pos hr, mul_comm t (Real.log r)]
    ring
  rw [Real.log_le_iff_le_exp hh, hpow]

/--
Real logarithmic-to-`rpow` equivalence with a positive multiplicative
constant, matching the constant shape of `ABCConjecture`.

For `h > 0`, `r > 0` and `K > 0`, `log h <= t * log r + log K` is equivalent
to `h <= K * r ^ t` for every real exponent `t`.
-/
theorem logLeIffLeMulRpow {h r K t : Real} (hh : 0 < h) (hr : 0 < r) (hK : 0 < K) :
    Real.log h ≤ t * Real.log r + Real.log K ↔ h ≤ K * r ^ t := by
  have h := logLeIffLeExpMulRpow (A := Real.log K) (t := t) hh hr
  rwa [Real.exp_log hK] at h

/--
The logarithmic (additive) form of the ABC bound with a fixed additive
constant `A`: `log c <= (1 + epsilon) * log (radical (a*b*c)) + A` on ABC
triples.
-/
def ABCLogBound (epsilon A : Real) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    Real.log (c : Real) ≤ (1 + epsilon) * Real.log (radical (a * b * c) : Real) + A

/--
The logarithmic form of the ABC conjecture: for every `epsilon > 0` there is
an additive constant `A` with `ABCLogBound epsilon A`.
-/
def ABCLogConjecture : Prop :=
  ∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ABCLogBound epsilon A

/-- For ABC triples the third entry is strictly positive, read off the
compiled denominator coordinate of `abcRationalPoint`. -/
theorem abcTriple_c_pos {a b c : Nat} (habc : IsABCTriple a b c) :
    (0 : Real) < (c : Real) := by
  have hden : (abcRationalPoint a c).den = c := abcRationalPoint_den habc
  have hc : 0 < c := by
    rw [← hden]
    exact Rat.den_pos _
  exact Nat.cast_pos.mpr hc

/-- The radical of a product of naturals is strictly positive. -/
theorem radical_cast_pos (a b c : Nat) : (0 : Real) < (radical (a * b * c) : Real) :=
  Nat.cast_pos.mpr (radical_pos (a * b * c))

/-- `Statement.radical` is definitionally the existing `natRadical` constant used by
`RationalPrimeSupport`.  This is an alias identification of the same constant, valid for
every `n` (no positivity premise is needed). -/
theorem radical_eq_natRadical (n : Nat) : radical n = natRadical n := rfl

/--
On ABC triples, `Real.log` of the radical of `a*b*c` is exactly the sibling arithmetic
weight of the compiled rational point.

This combines `radical_eq_natRadical` (alias identification) with the terminal
`arithmeticWeight_abcRationalPoint`; the only premise is `h : IsABCTriple a b c`, which is
what the sibling identity requires.
-/
theorem radical_log_eq_arithmeticWeight {a b c : Nat} (h : IsABCTriple a b c) :
    Real.log (radical (a * b * c) : Real) = arithmeticWeight (abcRationalPoint a c) := by
  rw [radical_eq_natRadical, arithmeticWeight_abcRationalPoint h]

/--
Per-`epsilon` equivalence between the logarithmic ABC estimate and the
literal radical-power inequality with a positive constant `K`.

Both sides existentially quantify a single constant that is independent of the
triple; the predicate `IsABCTriple`, the radical, the non-strict inequality and
the quantifier order are unchanged.
-/
theorem abcLogBound_exists_iff_rpow_exists (epsilon : Real) (_heps : 0 < epsilon) :
    (∃ A : Real, ABCLogBound epsilon A) ↔
      (∃ K : Real, 0 < K ∧
        ∀ a b c : Nat, IsABCTriple a b c →
          (c : Real) ≤ K * (radical (a * b * c) : Real) ^ (1 + epsilon)) := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨Real.exp A, Real.exp_pos A, ?_⟩
    intro a b c habc
    have hc : (0 : Real) < (c : Real) := abcTriple_c_pos habc
    have hr : (0 : Real) < (radical (a * b * c) : Real) := radical_cast_pos a b c
    exact (logLeIffLeExpMulRpow (A := A) (t := 1 + epsilon) hc hr).mp (hA a b c habc)
  · rintro ⟨K, hK, hKbound⟩
    refine ⟨Real.log K, ?_⟩
    intro a b c habc
    have hc : (0 : Real) < (c : Real) := abcTriple_c_pos habc
    have hr : (0 : Real) < (radical (a * b * c) : Real) := radical_cast_pos a b c
    exact (logLeIffLeMulRpow (K := K) (t := 1 + epsilon) hc hr hK).mpr (hKbound a b c habc)

/--
Height form of the same per-`epsilon` equivalence, stated with the IUT height
`Height.logHeight₁ (abcRationalPoint a c)` and reduced through the compiled
identity `abcRationalPoint_logHeight₁`.
-/
theorem abcLogHeightBound_exists_iff_rpow_exists (epsilon : Real) (heps : 0 < epsilon) :
    (∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * Real.log (radical (a * b * c) : Real) + A) ↔
      (∃ K : Real, 0 < K ∧
        ∀ a b c : Nat, IsABCTriple a b c →
          (c : Real) ≤ K * (radical (a * b * c) : Real) ^ (1 + epsilon)) := by
  have hiff :
      (∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
          Height.logHeight₁ (abcRationalPoint a c) ≤
            (1 + epsilon) * Real.log (radical (a * b * c) : Real) + A) ↔
        (∃ A : Real, ABCLogBound epsilon A) := by
    constructor
    · rintro ⟨A, hA⟩
      refine ⟨A, ?_⟩
      intro a b c habc
      rw [← abcRationalPoint_logHeight₁ habc]
      exact hA a b c habc
    · rintro ⟨A, hA⟩
      refine ⟨A, ?_⟩
      intro a b c habc
      rw [abcRationalPoint_logHeight₁ habc]
      exact hA a b c habc
  rw [hiff]
  exact abcLogBound_exists_iff_rpow_exists epsilon heps

end LeanFormal.IUT
