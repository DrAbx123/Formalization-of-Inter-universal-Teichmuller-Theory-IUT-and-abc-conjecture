import tmp.sheaf.xif.paper.S1952FiveIrreducibleActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1952IntegralityFive

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

@[reducible] def s1952NormedAlgebraOfEq {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (h : p = q) {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] :
    NormedAlgebra ℚ_[q] K := by
  subst h
  infer_instance

local instance s1952NormedAlgebraFive : NormedAlgebra ℚ_[5] concreteLogShellField :=
  s1952NormedAlgebraOfEq (p := concreteRationalPrime) (q := 5)
    concretePlace_rationalPrime_eq_five

/-- Pointwise integrality of the actual log shell at the S1487 five place. -/
def S1952IntegralLogShell : Prop :=
  (integralLogShell (K := CommonPrimeCompletion (K := GaussianField) S1487FivePlace)
    (p := 5) : Set (CommonPrimeCompletion (K := GaussianField) S1487FivePlace)) ⊆
    (Integers (CommonPrimeCompletion (K := GaussianField) S1487FivePlace) : Set _)

/-- **The actual integral log-shell is integral.** -/
theorem s1952IntegralLogShell_subset_integers :
    (integralLogShell (K := concreteLogShellField) (p := 5) : Set concreteLogShellField) ⊆
      (Integers concreteLogShellField : Set concreteLogShellField) := by
  intro x hx
  rcases hx with ⟨u, rfl⟩
  change (logShellScale 5 : concreteLogShellField)⁻¹ *
    unitLog (K := concreteLogShellField) u ∈ Integers concreteLogShellField
  have hpi : Irreducible (5 : Integers concreteLogShellField) := s1952Five_irreducible
  have hp2 : (5 : Nat) ≠ 2 := by norm_num
  have hmem := unitLog_mem_prime_smul_integers_of_odd_unramified
    (K := concreteLogShellField) (p := 5) hp2 hpi u
  rcases hmem with ⟨y, hy, hxy⟩
  have hxy' : (5 : concreteLogShellField) * y = unitLog
      (K := concreteLogShellField) u := by
    simpa [smul_eq_mul] using hxy
  have h5 : (logShellScale 5 : concreteLogShellField) = 5 := by
    norm_num [logShellScale]
  have h5ne : (5 : concreteLogShellField) ≠ 0 := by norm_num
  rw [h5, ← hxy', inv_mul_cancel_left₀ h5ne]
  exact hy

#print axioms s1952IntegralLogShell_subset_integers

end LeanFormal.IUT.XiFPaper.S1952IntegralityFive
end
