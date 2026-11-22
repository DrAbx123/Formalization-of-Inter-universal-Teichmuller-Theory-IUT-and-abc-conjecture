import LeanFormal.IUT.IUTIV.Estimates.ElementaryEstimates
import tmp.sheaf.xif.paper.ExpEst01StatementLedgerActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.IUTIV.Estimates

namespace LeanFormal.IUT.XiFPaper.ExpEst02ElementaryEstimatesActual

/-- Class B paper-input registration (B1): explicit PNT upper form
exists n0, forall n >= n0, n <= 4 * p n / (3 * log (p n)) for a prime-enumeration p
(Section1.lean:23; paper L913-926 via PNT).  Registered, not proved (Mathlib has PNT
asymptotics only). -/
def ExpEstPNTUpperPaperInput (p : Nat → Nat) : Prop :=
  ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n → (n : Real) ≤ 4 * (p n : Real) / (3 * Real.log (p n))

/-- Class B paper-input registration (B2): explicit bound on the sum of reciprocal
primes, in abstract prime-sum form (Section1.lean:24). -/
def ExpEstPrimeReciprocalSumPaperInput (primeSum : Real → Real) : Prop :=
  ∃ etaPrm : Real, 0 < etaPrm ∧ ∀ eta : Real, etaPrm ≤ eta →
    primeSum eta ≤ 4 * eta / (3 * Real.log eta)

/-- Class B paper-input registration (B3): explicit Chebyshev theta-function bound
shape used by IUT IV section 2 (Section2.lean:16-19): a bound
theta(eta) <= C * eta for an abstract theta function and constant C on eta >= eta0. -/
def ExpEstChebyshevThetaPaperInput (theta : Real → Real) : Prop :=
  ∃ eta0 : Real, ∃ C : Real, 0 < eta0 ∧ 0 < C ∧
    ∀ eta : Real, eta0 ≤ eta → theta eta ≤ C * eta

/-- CLASS A index: the tree's proved elementary estimates e1-e6 of IUT IV Thm 1.10
(ElementaryEstimates.lean:76/88/101/121/128/146) are PROVED and consumed directly
(no re-proof, no alias needed); listed here for the ExpEst ledger. -/
def s3135ExpEstClassAIndex : List (String × String) :=
  [ ("e1 arithmeticMean", "ElementaryEstimates.lean:76 iutIVThm110_e1_arithmeticMean (PROVED)"),
    ("e2 arithmeticMeanSquares", "ElementaryEstimates.lean:88 iutIVThm110_e2_arithmeticMeanSquares (PROVED)"),
    ("e3 card GL2 mod prime", "ElementaryEstimates.lean:101 iutIVThm110_e3_card_GL2_modPrime (PROVED)"),
    ("e4 card GL2 small primes", "ElementaryEstimates.lean:121 iutIVThm110_e4_card_GL2_smallPrimes (PROVED)"),
    ("e5 adjoin sqrt(-1) finrank", "ElementaryEstimates.lean:128 iutIVThm110_e5_adjoin_sqrtNegOne_finrank_le_two (PROVED)"),
    ("e6 logBounds", "ElementaryEstimates.lean:146 iutIVThm110_e6_logBounds (PROVED)"),
    ("sum_Icc_one", "ElementaryEstimates.lean:51 sum_Icc_one_cast (PROVED)"),
    ("sum_Icc_one_sq", "ElementaryEstimates.lean:63 sum_Icc_one_sq_cast (PROVED)") ]

theorem s3135ExpEstClassAIndex_length : s3135ExpEstClassAIndex.length = 8 := rfl

/-- CLASS B index: explicit PNT/Chebyshev paper inputs registered in this file. -/
def s3135ExpEstClassBIndex : List (String × String) :=
  [ ("B1 explicit PNT upper", "Section1.lean:23 (paper L913-926 via PNT); ExpEstPNTUpperPaperInput"),
    ("B2 prime reciprocal sum", "Section1.lean:24; ExpEstPrimeReciprocalSumPaperInput"),
    ("B3 Chebyshev theta", "Section2.lean:16-19; ExpEstChebyshevThetaPaperInput") ]

theorem s3135ExpEstClassBIndex_length : s3135ExpEstClassBIndex.length = 3 := rfl

#check iutIVThm110_e1_arithmeticMean
#check iutIVThm110_e6_logBounds
#check ExpEstPNTUpperPaperInput
#check ExpEstChebyshevThetaPaperInput

end LeanFormal.IUT.XiFPaper.ExpEst02ElementaryEstimatesActual
end
