/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIV.Estimates.ArithmeticDivisorDegree
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalDifferent
import Mathlib.Tactic

/-! # GAP-NORM-ARCH-C: abc base field ℚ and the arch normalization factor 1/[F:Q] -/

/-
| field | value |
|---|---|
| Status | green attempt: IUT IV arch normalization `heightWeight F = 1/[F:Q]` and `toricHeightWeight F = 1/(2[F:Q])` (ArithmeticDivisorDegree:1214/1217); for the rational ABC route base field ℚ they are `1` and `1/2`; general degree-one K conditional versions |
| Reuse | `ArithmeticDivisorDegree.lean:1214/1217`（heightWeight/toricHeightWeight，hArc/hToricArc 的因子）; `RationalDifferent.lean:27-40`（degree one ⇒ ℚ ≃ₐ K）; ABC statement `Statement.lean:26/28`（IsABCTriple/ABCInequality over Nat/ℚ） |
| GAP | ABC statement/route has no explicit number-field object K with a `[K:Q]` instance; the base field is ℚ only at the statement level. If the IUT-to-ABC step uses a general F, the factor is `1/[F:Q]` and equals 1 only for degree-one F. |
| 纪律 | no sorry/axiom; no new assumptions |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1NormArchCAbcActual

open LeanFormal.IUT.IUTIV.Estimates

/-- **IUT IV arch normalization over ℚ**: `heightWeight ℚ = 1/[ℚ:ℚ] = 1`. -/
theorem heightWeight_rat : heightWeight ℚ = 1 := by
  unfold heightWeight
  rw [CommSemiring.finrank_self]
  norm_num

/-- **IUT IV toric arch normalization over ℚ**: `toricHeightWeight ℚ = 1/(2[ℚ:ℚ]) = 1/2`. -/
theorem toricHeightWeight_rat : toricHeightWeight ℚ = 1 / 2 := by
  unfold toricHeightWeight
  rw [CommSemiring.finrank_self]
  norm_num

/-- Conditional form from `RationalDifferent.lean:27`: a number field of degree one has
arch normalization factor `1/[K:Q] = 1`. -/
theorem heightWeight_eq_one_of_finrank_one
    {K : Type*} [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 1) : heightWeight K = 1 := by
  unfold heightWeight
  rw [h]
  norm_num

/-- Conditional toric form: degree one gives `1/(2[K:Q]) = 1/2`. -/
theorem toricHeightWeight_eq_half_of_finrank_one
    {K : Type*} [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 1) : toricHeightWeight K = 1 / 2 := by
  unfold toricHeightWeight
  rw [h]
  norm_num

def normArchCAbcRows : List (String × String) :=
  [ ("heightWeight_rat", "h□ arch factor 1/[Q:Q] = 1 over the rational ABC base field") ,
    ("toricHeightWeight_rat", "h^tor arch factor 1/(2[Q:Q]) = 1/2") ,
    ("heightWeight_eq_one_of_finrank_one", "degree-one K conditional (RationalDifferent:27)") ,
    ("toricHeightWeight_eq_half_of_finrank_one", "degree-one K toric conditional") ,
    ("GAP-NORM-ARCH-C-K", "no explicit K object/[K:Q] instance in the ABC route; general F would need 1/[F:Q]") ]

theorem normArchCAbcRows_length : normArchCAbcRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1NormArchCAbcActual