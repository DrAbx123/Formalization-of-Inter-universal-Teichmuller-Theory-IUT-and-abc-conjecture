import tmp.sheaf.xif.paper.S1952FiveIrreducibleActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds

/-!
# S1952: the actual integral log-shell is integral

The actual completion of the S1487 five place is the normalized Gaussian
five-place completion.  The rational prime five is irreducible there
(S1952FiveIrreducibleActual).  The sharp odd-unramified shell bound then gives
unitLog u in 5 times the integer ring, so dividing by the shell scale 5 puts
every element of the integral log-shell in the integer ring.

No sorry, admit or axiom is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1952IntegralityActual

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

/-- Generic transport of a normed-algebra structure along an equality of the
rational prime. -/
@[reducible] def s1952NormedAlgebraOfEq {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (h : p = q) {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] :
    NormedAlgebra ℚ_[q] K := by
  subst h
  infer_instance

/-- The scalar-field structure at the literal rational prime five. -/
local instance s1952NormedAlgebraFive : NormedAlgebra ℚ_[5] concreteLogShellField :=
  s1952NormedAlgebraOfEq (p := concreteRationalPrime) (q := 5)
    concretePlace_rationalPrime_eq_five

/-- Pointwise integrality of the actual log shell at the S1487 five place. -/
def S1952IntegralLogShell : Prop :=
  (integralLogShell (K := CommonPrimeCompletion (K := GaussianField) S1487FivePlace)
    (p := 5) : Set (CommonPrimeCompletion (K := GaussianField) S1487FivePlace)) ⊆
    (Integers (CommonPrimeCompletion (K := GaussianField) S1487FivePlace) : Set _)

/-- **The actual integral log-shell is integral** at the completion's own
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

/-- **The actual integral log-shell is integral.** -/
theorem s1952IntegralLogShell_subset_integers :
    (integralLogShell (K := concreteLogShellField) (p := 5) : Set concreteLogShellField) ⊆
      (Integers concreteLogShellField : Set concreteLogShellField) := by
  have hpred : concreteRationalPrime = 5 := concretePlace_rationalPrime_eq_five
  have h := s1952IntegralLogShell_subset_integers_aux
  simpa [hpred] using h

/-- The S1952 pointwise integrality statement holds. -/
theorem s1952IntegralLogShell_holds : S1952IntegralLogShell := by
  intro x hx
  exact s1952IntegralLogShell_subset_integers hx

#print axioms s1952IntegralLogShell_subset_integers
#print axioms s1952IntegralLogShell_holds

end LeanFormal.IUT.XiFPaper.S1952IntegralityActual
end
