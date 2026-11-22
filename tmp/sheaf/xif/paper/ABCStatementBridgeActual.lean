/- ABCStatement bridge re-exports: coprime/radical form to IsABCTriple form and
back, hence an equivalence. -/
import tmp.sheaf.xif.paper.Mzk1ABCStatementBridgeActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.ABCStatementBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1ABCStatementBridgeActual

theorem abcStatement_to_ABCConjecture (h : ABCStatement) : ABCConjecture :=
  Mzk1ABCStatementBridgeActual.abcStatement_to_ABCConjecture h

theorem abcConjecture_to_abcStatement (h : ABCConjecture) : ABCStatement := by
  intro ε hε
  obtain ⟨K, hKpos, hK⟩ := h ε hε
  refine ⟨K, le_of_lt hKpos, ?_⟩
  intro a b c ha hb hc hsum hcop
  have htrip : IsABCTriple a b c := ⟨ha, hb, hsum, hcop⟩
  have hle : (c : Real) ≤
      K * Real.rpow (LeanFormal.IUT.radical (a * b * c) : Real) (1 + ε) :=
    hK a b c htrip
  have hrad : LeanFormal.IUT.radical (a * b * c) =
      Mzk1G1Actual.radical (a * b * c) :=
    (Mzk1ABCStatementBridgeActual.radical_eq (a * b * c)).symm
  calc (c : Real) ≤
      K * Real.rpow (LeanFormal.IUT.radical (a * b * c) : Real) (1 + ε) := hle
    _ = K * (Mzk1G1Actual.radical (a * b * c) : Real) ^ (1 + ε) := by
        rw [hrad, Real.rpow_eq_pow]

theorem abcStatement_iff_ABCConjecture : ABCStatement ↔ ABCConjecture :=
  ⟨abcStatement_to_ABCConjecture, abcConjecture_to_abcStatement⟩

#print axioms abcStatement_to_ABCConjecture
#print axioms abcConjecture_to_abcStatement
#print axioms abcStatement_iff_ABCConjecture

end LeanFormal.IUT.XiFPaper.ABCStatementBridgeActual
end
