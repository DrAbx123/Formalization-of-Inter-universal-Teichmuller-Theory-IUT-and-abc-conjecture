import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence

/-! Mainline: ABCLogConjecture equivalence with bound family and rpow form. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCLogEquivActual

open LeanFormal.IUT

theorem abcLogConjecture_iff_boundFamily :
    ABCLogConjecture ↔ ∀ (ε : Real), 0 < ε → ∃ A : Real, ABCLogBound ε A :=
  Iff.rfl

theorem abcLogBound_mono {ε A1 A2 : Real} (hA : A1 ≤ A2)
    (h : ABCLogBound ε A1) : ABCLogBound ε A2 := by
  intro a b c habc
  exact le_trans (h a b c habc) (by linarith)

theorem abcLogConjecture_iff_rpowFamily :
    ABCLogConjecture ↔
      ∀ (ε : Real), 0 < ε → ∃ K : Real, 0 < K ∧
        ∀ a b c : Nat, IsABCTriple a b c →
          (c : Real) ≤ K * (radical (a * b * c) : Real) ^ (1 + ε) := by
  constructor
  · intro H ε hε
    exact (abcLogBound_exists_iff_rpow_exists ε hε).mp (H ε hε)
  · intro H ε hε
    exact (abcLogBound_exists_iff_rpow_exists ε hε).mpr (H ε hε)

end LeanFormal.IUT.XiFPaper.Mzk1ABCLogEquivActual