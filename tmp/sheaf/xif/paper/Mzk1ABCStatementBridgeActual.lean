/- ABC statement bridge: the coprime/radical form `ABCStatement` implies the
`IsABCTriple`-form `ABCConjecture`.  The radical conventions agree definitionally
(both the product of the distinct prime factors). -/
import tmp.sheaf.xif.paper.Mzk1G1ABCCompactnessActual
import LeanFormal.IUT.ABCBridge.Statement
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ABCStatementBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual

/-- The G1 paper radical (prime-factor-list product) is the project radical. -/
theorem radical_eq (n : Nat) :
    Mzk1G1Actual.radical n = LeanFormal.IUT.radical n := by
  show Mzk1G1Actual.radical n = LeanFormal.IUT.natRadical n
  rw [LeanFormal.IUT.natRadical_eq_prod_primeFactors]
  rfl

/-- Actual bridge: `ABCStatement` (coprime/radical form) implies
`ABCConjecture` (IsABCTriple form). -/
theorem abcStatement_to_ABCConjecture (h : ABCStatement) : ABCConjecture := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h ε hε
  refine ⟨max C 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  · intro a b c htrip
    rcases htrip with ⟨ha, hb, hsum, hcop⟩
    have hc : 0 < c := by omega
    have hle := hbound a b c ha hb hc hsum hcop
    have hrad : Mzk1G1Actual.radical (a * b * c) = LeanFormal.IUT.radical (a * b * c) :=
      radical_eq (a * b * c)
    have hCle : C ≤ max C 1 := le_max_left C 1
    have hrpow : 0 ≤ Real.rpow (LeanFormal.IUT.radical (a * b * c) : Real) (1 + ε) :=
      Real.rpow_nonneg (by positivity) _
    calc (c : Real) ≤ C * (Mzk1G1Actual.radical (a * b * c) : Real) ^ (1 + ε) := hle
      _ = C * Real.rpow (LeanFormal.IUT.radical (a * b * c) : Real) (1 + ε) := by
          rw [hrad]
          rw [Real.rpow_eq_pow]
      _ ≤ max C 1 * Real.rpow (LeanFormal.IUT.radical (a * b * c) : Real) (1 + ε) :=
          mul_le_mul_of_nonneg_right hCle hrpow

#print axioms radical_eq
#print axioms abcStatement_to_ABCConjecture

end LeanFormal.IUT.XiFPaper.Mzk1ABCStatementBridgeActual
end
