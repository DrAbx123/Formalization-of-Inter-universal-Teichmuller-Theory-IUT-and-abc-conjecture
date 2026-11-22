import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import Mathlib.Tactic

/-!
# shehdd A681 Gap2 arithmetic reduction gate (Sha, read-only)

Consumes the GREEN mainline Gap2 arithmetic reduction
(`Mzk1Gap2ArithmeticReductionActual`):
* `logN_le_log_c_add_log3` (arithmetic core);
* `correctedGap2_reduces_to_radical` (Gap2 reduces to the radical form);
and records the remaining named input (the radical/arithmetic inequality itself).

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionShaActual

structure Gap2ArithmeticRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def gap2ArithmeticRows : List Gap2ArithmeticRow :=
  [ ⟨"log support estimate", "mainline logN_le_log_c_add_log3 (gate trio)", "GREEN"⟩
  , ⟨"Gap2 arithmetic reduction", "mainline correctedGap2_reduces_to_radical (gate trio)", "GREEN"⟩
  , ⟨"remaining named input", "the radical/arithmetic inequality itself", "NAMED"⟩
  , ⟨"scope", "gate only; no gap claimed", "INTEGRITY"⟩
  ]

theorem gap2ArithmeticRows_length : gap2ArithmeticRows.length = 4 := rfl

theorem gap2ArithmeticRows_statuses_ok :
    gap2ArithmeticRows.all (fun r =>
      r.status ∈ ["GREEN", "NAMED", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionShaActual

/-! ### Axiom gates (mainline Gap2 arithmetic reduction, read-only) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.logN_le_log_c_add_log3
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.correctedGap2_reduces_to_radical
