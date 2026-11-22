/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1A703CorrectionQpilotActual — A703 correction / retraction record (qpilot)

Per lead A703 (user review): the `hfull` condition of `final_conditional_ABC` is
UNSATISFIABLE for fixed T (N = a+b+c+1 runs over all odd numbers >= 5, so a prime
outside the finite bad set appears), hence `final_conditional_ABC` and
`natRadicalWeightBound_iff_ABC` are VACUOUS and RETRACTED.  The N-scaling is not the
paper structure; the paper bad primes are the prime divisors of abc and weights are
normalized by `[F_v:Q_p]/[F:Q]`.  The old qpilot files that depend on the
hfull/N-scaling interface are historical and RETRACTED; this file records the
corrected triple-dependent Θ-data specification (no hfull, no N-scaling) with its
arithmetic coherence lemmas. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1A703CorrectionQpilotActual

universe u

open scoped BigOperators

/-! ### Retraction / status table -/

/-- A703 status rows (three states: RETRACTED / CORRECTED / STILL-VALID). -/
def a703StatusRows : List (String × String × String) :=
  [ ("final_conditional_ABC (hfull, N=a+b+c+1)", "RETRACTED / VACUOUS",
     "hfull unsatisfiable: prime outside finite bad set"),
    ("natRadicalWeightBound_iff_ABC (N-scaling)", "VACUOUS (as used)",
     "vacuous with the unsatisfiable hfull"),
    ("N = a+b+c+1 scaling", "NOT PAPER STRUCTURE",
     "paper bad primes = prime divisors of abc; weights normalized"),
    ("3.12 chain load-bearing via thetaReading", "NOT LOAD-BEARING",
     "thetaReading has no upper bound"),
    ("triple-dependent Theta-data (corrected)", "CORRECTED SPEC (this file)",
     "bad support = primes(abc), q=(abc)^2, normalized weights"),
    ("qpilot Mathlib-only Gap1/Gap2 arithmetic", "STILL VALID",
     "independent of hfull/N-scaling") ]

theorem a703StatusRows_length : a703StatusRows.length = 6 := rfl

/-! ### Corrected triple-dependent Theta-data specification -/

/-- Corrected triple-dependent Θ-data: bad support = prime divisors of the triple,
`q = (abc)^2`, normalized weight over the bad support.  No `hfull`, no N-scaling. -/
structure CorrectedTripleThetaData (a b c : Nat) where
  /-- the bad-prime support: exactly the prime divisors of `a*b*c`. -/
  badSupport : Finset Nat
  badSupport_eq : ∀ p : Nat, p ∈ badSupport ↔ p.Prime ∧ p ∣ a * b * c
  /-- the q value is `(abc)^2`. -/
  q : Nat
  q_def : q = (a * b * c) ^ 2
  /-- `q`-log reading. -/
  qLog : Real
  qLog_eq : qLog = 2 * Real.log (a * b * c)

/-- The normalized weight `Σ_{p | abc} log p`. -/
noncomputable def normalizedWeight {a b c : Nat} (D : CorrectedTripleThetaData a b c) :
    Real :=
  D.badSupport.sum (fun p => Real.log (p : Real))

/-- Arithmetic coherence: `(1/6)·log q = (1/3)·log(abc)` for `q = (abc)^2`. -/
theorem sixth_qLog_eq_third_log_abc {a b c : Nat} (D : CorrectedTripleThetaData a b c)
    (habc : 0 < a * b * c) :
    D.qLog / 6 = Real.log (a * b * c) / 3 := by
  rw [D.qLog_eq]
  ring

/-- The normalized weight is the sum of logs over the bad support (definitional). -/
theorem normalizedWeight_eq {a b c : Nat} (D : CorrectedTripleThetaData a b c) :
    normalizedWeight D = D.badSupport.sum (fun p => Real.log (p : Real)) := rfl

/-- No `hfull` occurs in the corrected data: the bad support is the *actual* prime
divisor support and needs no odd-number surjectivity. -/
theorem corrected_data_no_hfull {a b c : Nat} (D : CorrectedTripleThetaData a b c) :
    (∀ p : Nat, p ∈ D.badSupport ↔ p.Prime ∧ p ∣ a * b * c) ∧ D.q = (a * b * c) ^ 2 :=
  ⟨D.badSupport_eq, D.q_def⟩

/-! ### Retracted qpilot files (historical) -/

/-- The historical qpilot files that used the retracted hfull/N-scaling interface;
their contents are preserved as history and must not be cited as evidence. -/
def retractedQpilotFiles : List String :=
  [ "Mzk1FinalBoundaryV2QpilotActual (hfull-based canonical re-export)",
    "Mzk1FinalSemanticsAuditQpilotActual (canonical V2 re-export)",
    "Mzk1LaneFinalReportQpilotActual (V2 rows)",
    "Mzk1CanonicalLandingQpilotActual (canonical carrier re-export)",
    "Mzk1CarrierBadInvSupplementQpilotActual (canonical carrier re-export)" ]

theorem retractedQpilotFiles_length : retractedQpilotFiles.length = 5 := rfl

#check a703StatusRows_length
#check sixth_qLog_eq_third_log_abc
#check corrected_data_no_hfull
#check retractedQpilotFiles_length

end LeanFormal.IUT.XiFPaper.Mzk1A703CorrectionQpilotActual
end
