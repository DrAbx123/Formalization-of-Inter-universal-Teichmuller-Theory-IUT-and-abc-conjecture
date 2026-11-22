import LeanFormal.IUT.Foundations.Theta.OddTheta

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: EtTh|etale theta|theta function|theta group|q-pilot|Theta-pilot|Frobenioid.*theta -> 226 LeanFormal + 1502 paper + 10 archive + 9 gap + 143 vendor + 175 corpus hits -> reuse: LeanFormal/IUT/Foundations/Theta/OddTheta.lean:75/80/84/88 actual odd theta series, :94 signal law, :98 norm, :103 additivity, :126/211 exponent; OddThetaShift.lean:14 oddTheta_shift; OddThetaNormalization.lean:14/29/45 quotient eval -> REUSE (aliases; no re-proof).

# [EtTh] 01: object layer - the actual odd theta series (EtTh Prop 1.4)

Corpus: papers/motizuki_corpus/text/The Etale Theta Function and its Frobenioid-theoretic
Manifestations.txt, Proposition 1.4 (text line 1338):
Theta(q,U) = q^(-1/8) * sum_{n in Z} (-1)^n q^((n+1/2)^2/2) U^(2n+1); removing q^(-1/8),
oddThetaTerm(q,U,n) = (-1)^n q^(n(n+1)/2) U^(2n+1), oddTheta = its integer tsum.
Tree realization reused here (no re-proof): oddThetaTerm:84, oddTheta:88, sign
(-1)^n and norm facts :94/:98/:103, exponent bookkeeping :126/:211, convergence
criterion :164.  Class A (algebraic bookkeeping) reused; the analytic
convergence/shift/evaluation are separately proved in OddThetaShift/Normalization.
-/

namespace LeanFormal.IUT.XiFPaper.EtTh01OddThetaSeriesActual

open LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- The sign factor (-1)^n in L (reused from OddTheta:94). -/
theorem etTh_oddThetaSign_eq_pow (n : ℤ) :
    oddThetaSign (L := L) n = (-1 : L) ^ n :=
  oddThetaSign_eq_pow (L := L) n

/-- The sign factor has norm one (reused from OddTheta:98). -/
theorem etTh_norm_oddThetaSign (n : ℤ) :
    ‖oddThetaSign (L := L) n‖ = 1 :=
  norm_oddThetaSign (L := L) n

/-- The sign factor is additive in the exponent (reused from OddTheta:103). -/
theorem etTh_oddThetaSign_add (m n : ℤ) :
    oddThetaSign (L := L) (m + n) =
      oddThetaSign (L := L) m * oddThetaSign (L := L) n :=
  oddThetaSign_add (L := L) m n

#check etTh_oddThetaSign_eq_pow
#check etTh_norm_oddThetaSign
#check etTh_oddThetaSign_add

end LeanFormal.IUT.XiFPaper.EtTh01OddThetaSeriesActual