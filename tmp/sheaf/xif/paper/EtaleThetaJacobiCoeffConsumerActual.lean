import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing
import tmp.sheaf.xif.paper.JacobiFormalProductExpansions

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing
open LeanFormal.IUT.XiFPaper.TateJacobiHahnAttempt

namespace LeanFormal.IUT.XiFPaper.EtaleThetaJacobiCoeffConsumerActual

universe u

/-- Exponent-pair consumer: the two theta terms n and -n-1 have
    the same q_X-exponent and opposite U-exponent. -/
theorem theta_exponent_pair_consumer (n : Int) :
    thetaQExponent (-n - 1) = thetaQExponent n ∧
      thetaUExponent (-n - 1) = -thetaUExponent n :=
  ⟨thetaQExponent_neg_succ n, thetaUExponent_neg_succ n⟩

/-- Jacobi coefficient consumer: finite Jacobi product coefficient equals
    the coefficient of the triple q-binomial expansion. -/
theorem jacobi_coeff_consumer (K : Type u) [Field K] (z : K) (N : Nat) (k : Int) :
    (jacobiFormalProduct z N).coeff k =
      ((Finset.sum (Finset.range (N + 1)) (fun j : Nat =>
          LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinoTermC
            (K := HahnSeries Int K) N j (formalR ^ 4)
            (HahnSeries.C z * formalR ^ 2))) *
        (Finset.sum (Finset.range (N + 1)) (fun j : Nat =>
          LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinoTermC
            (K := HahnSeries Int K) N j (formalR ^ 4)
            (HahnSeries.C z⁻¹ * formalR ^ 2))) *
          (Finset.sum (Finset.range (N + 1)) (fun j : Nat =>
            LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinoTermC
              (K := HahnSeries Int K) N j (formalR ^ 4)
              (-(formalR ^ 4))))).coeff k := by
  rw [LeanFormal.IUT.XiFPaper.JacobiFormalProductExpansions.jacobiFormalProduct_eq_threeExpansions]

#check theta_exponent_pair_consumer
#check jacobi_coeff_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaJacobiCoeffConsumerActual
