/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1TripleThetaModelActual
import tmp.sheaf.xif.paper.Mzk1A703CorrectionQpilotActual
import tmp.sheaf.xif.paper.Mzk1WeightNormalizationActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

/-!
# A707 N1 canonical summary: triple-dependent Theta-data (mainline)

A single structure `TripleThetaData a b c` unifying the three corrected pieces:
* bad support = prime divisors of `a*b*c` (abc model);
* `q = (abc)^2`, `qLog = 2 log(abc)`, `(1/6) qLog = (1/3) log(abc)`;
* bounded-region estimate `c^2 <= K·a·b => 3 log c <= log(abc) + log K`;
* normalized weight `Σ_{p|abc} log p = log (natRadical(abc))` (hull normalization).

No `hfull`, no `N = a+b+c+1` scaling.  No canonical change; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1N1CanonicalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1TripleThetaModelActual
open LeanFormal.IUT.XiFPaper.Mzk1A703CorrectionQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1WeightNormalizationActual

/-- Unified triple-dependent Theta-data (extends the corrected q-pilot data). -/
structure TripleThetaData (a b c : Nat)
    extends CorrectedTripleThetaData a b c where

/-- The normalized weight over the triple's bad support. -/
noncomputable def tripleWeight {a b c : Nat} (D : TripleThetaData a b c) : Real :=
  D.badSupport.sum (fun p => Real.log (p : Real))

/-- Bad support is exactly the prime-factor set of `a*b*c`. -/
theorem badSupport_eq_primeFactors {a b c : Nat} (D : TripleThetaData a b c)
    (habc : 0 < a * b * c) :
    D.badSupport = (a * b * c).primeFactors := by
  ext p
  rw [D.badSupport_eq, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdvd⟩
    exact ⟨hp, hdvd, ne_of_gt habc⟩
  · rintro ⟨hp, hdvd, _⟩
    exact ⟨hp, hdvd⟩
/-- `q` is `(a*b*c)^2`. -/
theorem q_eq_sq {a b c : Nat} (D : TripleThetaData a b c) :
    D.q = (a * b * c) ^ 2 :=
  D.q_def

/-- `qLog = 2 log(abc)`. -/
theorem qLog_eq_twice {a b c : Nat} (D : TripleThetaData a b c) :
    D.qLog = 2 * Real.log (a * b * c : Real) :=
  D.qLog_eq

/-- `(1/6) qLog = (1/3) log(abc)`. -/
theorem sixth_qLog_eq_third {a b c : Nat} (D : TripleThetaData a b c) :
    D.qLog / 6 = Real.log (a * b * c : Real) / 3 := by
  rw [D.qLog_eq]
  ring

/-- Bounded-region estimate (`c^2 <= K ab` ⇒ `3 log c <= log(abc) + log K`). -/
theorem bounded_log_c_le_third {a b c : Nat} {K : Real}
    (hc : 0 < c) (habc : 0 < a * b * c) (hK : 0 < K)
    (hbdd : ((c : Real) ^ 2) ≤ K * ((a * b : Nat) : Real)) :
    3 * Real.log (c : Real) ≤ Real.log (((a * b * c : Nat)) : Real) + Real.log K :=
  Mzk1TripleThetaModelActual.bounded_log_c_le_third hc habc hK hbdd

/-- The (hull-normalized) triple weight equals `log (natRadical(abc))`. -/
theorem tripleWeight_eq_radical {a b c : Nat} (D : TripleThetaData a b c)
    (habc : 0 < a * b * c) :
    tripleWeight D = Real.log (natRadical (a * b * c) : Real) := by
  unfold tripleWeight
  rw [badSupport_eq_primeFactors D habc]
  exact Mzk1WeightNormalizationActual.tripleNormalizedWeight_eq_radical a b c

/-- Scope rows of the N1 canonical summary. -/
def n1Rows : List (String × String) :=
  [ ("bad support", "= (a*b*c).primeFactors (PROVED)"),
    ("q-pilot", "q = (abc)^2; qLog = 2 log(abc) (PROVED)"),
    ("(1/6) qLog", "= (1/3) log(abc) (PROVED)"),
    ("bounded region", "c^2 <= K ab => 3 log c <= log(abc)+log K (PROVED)"),
    ("normalized weight", "Σ_{p|abc} log p = log natRadical(abc) (PROVED)"),
    ("scope", "no hfull/N-scaling; ABC gate NOT passed; no canonical change") ]

theorem n1Rows_length : n1Rows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1N1CanonicalActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1N1CanonicalActual.badSupport_eq_primeFactors
#print axioms LeanFormal.IUT.XiFPaper.Mzk1N1CanonicalActual.tripleWeight_eq_radical
#print axioms LeanFormal.IUT.XiFPaper.Mzk1N1CanonicalActual.n1Rows_length