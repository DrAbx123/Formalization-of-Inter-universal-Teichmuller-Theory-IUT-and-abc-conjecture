import LeanFormal/IUT/IUTII/Frobenioid/Example36FrobeniusValueAction
import LeanFormal/IUT/IUTII/Frobenioid/Example36LogShellFrobeniusAction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1Example36FrobeniusLawChainActual — A479 real packages (Example 3.6 Frobenius laws)

New conclusions combining the concrete Frobenius scaling laws of
`Example36FrobeniusValueAction.lean` (:185/:194/:203/:218) and the log-shell
p-scaling laws of `Example36LogShellFrobeniusAction.lean` (:140/:163/:175/:185):

1. `principalDivisor_frobenius_package`: finite and archimedean principal
   divisors scale by `n` under the `n`-th power;
2. `sourceModelPrincipalDivisor_frobenius_package`: the value-coordinate and
   arithmetic-divisor forms of the same Frobenius scaling;
3. `integralLogShell_p_scaling_package`: p-scaling preserves the principal-unit
   and integral log-shell (and its lattice), and is nontrivial.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Example36FrobeniusLawChainActual

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.FrobeniusValueAction
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellFrobeniusAction

/-- Joint principal-divisor Frobenius scaling package. -/
theorem principalDivisor_frobenius_package {F : Type*} [Field F] [NumberField F]
    (f : Fˣ) (n : Nat) :
    principalDivisorFinite (f ^ n) = n • principalDivisorFinite f ∧
      principalDivisorInfinite (f ^ n) = n • principalDivisorInfinite f :=
  ⟨principalDivisorFinite_pow f n, principalDivisorInfinite_pow f n⟩

/-- Joint value-coordinate/arithmetic Frobenius scaling package. -/
theorem sourceModelPrincipalDivisor_frobenius_package {F : Type*} [Field F] [NumberField F]
    (D : GlobalPlaceData F) (hD : D.HasFiniteSupport) (f : Fˣ) (n : Nat) :
    sourceModelPrincipalDivisor D hD (f ^ n) = n • sourceModelPrincipalDivisor D hD f ∧
      arithmeticDivisor (sourceModelPrincipalDivisor D hD (f ^ n)) =
        n • arithmeticDivisor (sourceModelPrincipalDivisor D hD f) :=
  ⟨sourceModelPrincipalDivisor_pow D hD f n,
   arithmeticDivisor_sourceModelPrincipalDivisor_pow D hD f n⟩

/-- Joint log-shell p-scaling package (principal-unit/integral/lattice laws and
nontriviality). -/
theorem integralLogShell_p_scaling_package :
    (∀ x ∈ integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime),
        (concreteRationalPrime : concreteLogShellField) * x ∈
          integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)) ∧
      (∀ x ∈ integralLogShellLattice (K := concreteLogShellField)
          (p := concreteRationalPrime),
        (concreteRationalPrime : ℤ_[concreteRationalPrime]) • x ∈
          integralLogShellLattice (K := concreteLogShellField)
            (p := concreteRationalPrime)) ∧
      (∃ x : concreteLogShellField,
        x ∈ integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) ∧
          (concreteRationalPrime : concreteLogShellField) * x ≠ x) :=
  ⟨fun _ hx => integralLogShell_p_mul_mem hx,
   fun _ hx => integralLogShellLattice_p_smul_mem _ hx,
   integralLogShell_p_scaling_nontrivial⟩

#check principalDivisor_frobenius_package
#check integralLogShell_p_scaling_package

end LeanFormal.IUT.XiFPaper.Mzk1Example36FrobeniusLawChainActual
end