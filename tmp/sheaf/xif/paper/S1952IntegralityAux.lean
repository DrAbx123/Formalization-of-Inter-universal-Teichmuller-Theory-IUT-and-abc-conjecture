import tmp.sheaf.xif.paper.S1952FiveIrreducibleActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1952IntegralityAux

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S1952FiveIrreducibleActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm

local instance s1952GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1952FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The actual integral log-shell is integral, stated at the completion's own
rational prime. -/
theorem s1952IntegralLogShell_subset_integers_aux :
    (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) :
        Set concreteLogShellField) ⊆
      (Integers concreteLogShellField : Set concreteLogShellField) := by
  intro x hx
  rcases hx with ⟨u, rfl⟩
  change (logShellScale concreteRationalPrime : concreteLogShellField)⁻¹ *
    unitLog (K := concreteLogShellField) u ∈ Integers concreteLogShellField
  have hpred : concreteRationalPrime = 5 := concretePlace_rationalPrime_eq_five
  have hpi : Irreducible (concreteRationalPrime : Integers concreteLogShellField) := by
    rw [hpred]
    exact s1952Five_irreducible
  have hp2 : concreteRationalPrime ≠ 2 := by
    rw [hpred]
    norm_num
  have hmem := unitLog_mem_prime_smul_integers_of_odd_unramified
    (K := concreteLogShellField) (p := concreteRationalPrime) hp2 hpi u
  rcases hmem with ⟨y, hy, hxy⟩
  have hxy' : (concreteRationalPrime : concreteLogShellField) * y = unitLog
      (K := concreteLogShellField) u := by
    simpa [smul_eq_mul] using hxy
  have h5 : (logShellScale concreteRationalPrime : concreteLogShellField) =
      concreteRationalPrime := by
    rw [hpred]
    norm_num [logShellScale]
  have h5ne : (concreteRationalPrime : concreteLogShellField) ≠ 0 := by
    rw [hpred]
    norm_num
  rw [h5, ← hxy', inv_mul_cancel_left₀ h5ne]
  exact hy

#print axioms s1952IntegralLogShell_subset_integers_aux

end LeanFormal.IUT.XiFPaper.S1952IntegralityAux
end
