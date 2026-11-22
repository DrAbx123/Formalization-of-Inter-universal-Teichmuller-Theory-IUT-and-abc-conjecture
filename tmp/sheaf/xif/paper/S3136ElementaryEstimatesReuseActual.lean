import LeanFormal.IUT.IUTIV.Estimates.ElementaryEstimates

/-! # Stage-4 host: reuse of the IUT IV elementary estimates e1-e6

PRIOR ART (§7.9, checked first): LeanFormal/IUT/IUTIV/Estimates/ElementaryEstimates.lean:
:76 e1 arithmeticMean, :88 e2 arithmeticMeanSquares, :101 e3 card GL2 mod prime,
:121 e4 small primes, :128 e5 adjoin sqrt(-1) finrank <= 2, :146 e6 log bounds
(IV L1387-1407) - all formalized in the repo.  These are CLASS A inputs of the
Theorem 1.10 proof (used by the weighted-average side: collection averages over
j and j^2 correspond to e1/e2).

CONSUMER: weighted-average side of (c) / Theorem 1.10 skeleton.  This file reuses
the estimates through thin adapters (no re-proof) and records the correspondences.

LABEL: reuse adapters (class A prior art). Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ElementaryEstimatesReuseActual

open LeanFormal.IUT.IUTIV.Estimates

/-- Reuse (E1): arithmetic mean of j = 1..n. -/
theorem lgpE1_arithmeticMean (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) * (∑ m ∈ Finset.Icc 1 n, (m : ℝ)) = ((n : ℝ) + 1) / 2 :=
  iutIVThm110_e1_arithmeticMean n hn

/-- Reuse (E2): arithmetic mean of squares j^2 = 1..n. -/
theorem lgpE2_arithmeticMeanSquares (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) * (∑ m ∈ Finset.Icc 1 n, (m : ℝ) ^ 2) =
      (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / 6 :=
  iutIVThm110_e2_arithmeticMeanSquares n hn

/-- Reuse (E3): |GL2(F_p)| order. -/
theorem lgpE3_card_GL2_modPrime (p : ℕ) (hp : p.Prime) :
    Nat.card (GL (Fin 2) (ZMod p)) = p * (p + 1) * (p - 1) ^ 2 :=
  iutIVThm110_e3_card_GL2_modPrime p hp

/-- Reuse (E6): logarithmic bounds for 2,3,pi,5. -/
theorem lgpE6_logBounds :
    (0 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 ∧
      (1 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ Real.log Real.pi ∧
        Real.log Real.pi ≤ Real.log 5 ∧ Real.log 5 ≤ 2 :=
  iutIVThm110_e6_logBounds

/-- Correspondence rows: collection averages <-> IV elementary estimates. -/
def lgpElementaryCorrespondence : List (String × String) :=
  [ ("Step V collection sum over j", "(E1) arithmeticMean (IV L1387-1392)"),
    ("Step V collection sum over j^2 (theta label weights)", "(E2) arithmeticMeanSquares (IV L1393-1398)"),
    ("|GL2(F_p)| in the label counting", "(E3)/(E4) card_GL2 (IV L1402-1405)"),
    ("sqrt(-1) adjunction finrank", "(E5) adjoin_sqrtNegOne_finrank_le_two (IV L1406)"),
    ("numeric log bounds 2,3,pi,5", "(E6) logBounds (IV L1407)") ]

theorem lgpElementaryCorrespondence_length : lgpElementaryCorrespondence.length = 5 := rfl

#check lgpE1_arithmeticMean
#check lgpE2_arithmeticMeanSquares
#check lgpE3_card_GL2_modPrime
#check lgpE6_logBounds
#check lgpElementaryCorrespondence_length

end LeanFormal.IUT.XiFPaper.S3136ElementaryEstimatesReuseActual
end