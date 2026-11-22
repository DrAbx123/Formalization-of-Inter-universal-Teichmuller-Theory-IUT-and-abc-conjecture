import tmp.sheaf.xif.paper.Mzk1CorrectedRegionGap1Actual

/-! # Mzk1Stage4A703CorrectionActual (stage4 lane; A703 correction record)

**A703 (lead, per user audit)**: `final_conditional_ABC`'s `hfull` hypothesis is
UNSATISFIABLE for fixed `T` (the identity `a+b+c+1 = ∏_b p_b^{e_b}` cannot hold for all
ABC triples since the left side is unbounded while the right side is fixed).  Hence the
`corrected_gap1_of_fullSupport` route is VACUOUS and the `N = a+b+c+1` scaling is NOT the
paper structure (paper bad primes = prime factors of abc).  The old chain is kept as
historical and marked RETRACTED; this file adds the machine proof of the vacuity and the
retraction ledger.  No old file is modified.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4A703CorrectionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionGap1Actual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **A703 machine proof of the vacuity**: the `hfull` hypothesis of
`corrected_gap1_of_fullSupport` is unsatisfiable for fixed `T` and `e`.  Reason: it
would force `1+2+3+1 = ∏_b p_b^{e_b}` AND `2+3+5+1 = ∏_b p_b^{e_b}` (both are ABC
triples), i.e. `7 = 11`. -/
theorem hfull_unsatisfiable (e : Bad (nativePlaceSelection T) → Nat) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        a + b + c + 1 = ∏ b : Bad (nativePlaceSelection T),
          (qVFamTensorP T b) ^ (e b)) := by
  intro hfull
  have h123 : IsABCTriple 1 2 3 := by
    unfold IsABCTriple PrimitiveAdditiveTriple
    decide
  have h235 : IsABCTriple 2 3 5 := by
    unfold IsABCTriple PrimitiveAdditiveTriple
    decide
  have h1 := hfull 1 2 3 h123
  have h2 := hfull 2 3 5 h235
  rw [show (1 + 2 + 3 + 1 : Nat) = 7 by norm_num] at h1
  rw [show (2 + 3 + 5 + 1 : Nat) = 11 by norm_num] at h2
  omega

/-- **A703 consequence**: the hypothesis package of `corrected_gap1_of_fullSupport` is
inconsistent (the theorem is vacuously true and cannot bear the 3.12 chain). -/
theorem corrected_gap1_hypotheses_inconsistent
    (point : Nat → Nat → Nat → S1902Carrier T)
    (e : Bad (nativePlaceSelection T) → Nat)
    (hfull : ∀ a b c : Nat, IsABCTriple a b c →
      a + b + c + 1 = ∏ b : Bad (nativePlaceSelection T),
        (qVFamTensorP T b) ^ (e b)) :
    False :=
  hfull_unsatisfiable T e hfull

/-- The A703 retraction ledger for the stage4 lane: files whose status must be read as
RETRACTED/historical (they use `hfull` / `N = a+b+c+1` scaling). -/
def retractionLedger : List (String × String) :=
  [ ("Mzk1Stage4UnconditionalGap1AuditActual", "references corrected_gap1 (hfull route) — RETRACTED")
  , ("Mzk1Stage4FinalBoundaryV2AuditActual", "V2 gate semantics based on fullSupport route — RETRACTED")
  , ("Mzk1Stage4FinalSemanticsRegistryActual", "rows ② (corrected-region Gap1 THEOREM) based on hfull — RETRACTED")
  , ("Mzk1Stage4CorrectedRegionGap1ConsumerActual", "consumes corrected_gap1_of_fullSupport — vacuous")
  , ("Mzk1Stage4CorrectedRegionAssemblyActual", "assembles corrected-region path with hfull — historical")
  , ("Mzk1Stage4BadSumTightnessActual", "uses N = a+b+c+1 scaling (log N) — not the paper structure")
  , ("Mzk1Stage4Gap1ScalingLawConsumerActual", "uses FullRatio = a+b+c+1 (N-scaling) — RETRACTED")
  , ("Mzk1Stage4Gap1WiringActual", "wired FullRatio N-scaling — RETRACTED")
  , ("Mzk1Stage4BadSumNatRadicalActual", "BadSumWeightBound itself is pure arithmetic; the hfull route above it is retracted")
  , ("Mzk1Stage4CorrectedRegionB1SupportActual / B2SupportActual", "supporting lemmas for the retracted route; kept historical")
  ]

/-- The retraction ledger has ten rows. -/
theorem retractionLedger_length : retractionLedger.length = 10 := rfl

/-- A703 directive for future stage4 files: use triple-dependent Theta-data, NOT `hfull`
and NOT `N = a+b+c+1` scaling; paper weight is the normalized `Σ_{p|abc} log p`. -/
def a703Directive : List String :=
  [ "do NOT use hfull / fullSupport; it is machine-proved unsatisfiable",
    "do NOT use N = a+b+c+1 scaling; paper bad primes = primes of abc",
    "use normalizedWeight = Σ_{p|abc} log p (with [F_v:Q_p]/[F:Q] normalization)",
    "old chain kept as history with RETRACTED label; no 3.12 chain load-bearing claim"
  ]

#print axioms hfull_unsatisfiable
#check hfull_unsatisfiable
#check corrected_gap1_hypotheses_inconsistent
#check retractionLedger_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4A703CorrectionActual
end
