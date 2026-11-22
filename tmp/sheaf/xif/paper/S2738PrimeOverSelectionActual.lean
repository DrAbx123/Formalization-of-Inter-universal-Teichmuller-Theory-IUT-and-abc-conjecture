import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Over
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open scoped BigOperators nonZeroDivisors
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2738PrimeOverSelectionActual

open LeanFormal.IUT

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- A chosen prime of O_K over the rational prime `p`. -/
noncomputable def selectedPrimeOver (p : Nat) [Fact p.Prime] :
    Ideal (NumberField.RingOfIntegers K) :=
  Classical.choose (Ideal.nonempty_primesOver
    (Ideal.span {(p : ℤ)}) (S := NumberField.RingOfIntegers K))

theorem selectedPrimeOver_mem (p : Nat) [Fact p.Prime] :
    selectedPrimeOver K p ∈
      (Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K) :=
  Classical.choose_spec (Ideal.nonempty_primesOver
    (Ideal.span {(p : ℤ)}) (S := NumberField.RingOfIntegers K))

/-- Every prime in a finite rational support has an actual chosen prime of O_K
lying over it. -/
theorem exists_primeOver_of_mem_support
    (S : Finset Nat)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    ∀ p ∈ S, ∃ P : Ideal (NumberField.RingOfIntegers K),
      P ∈ (Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K) := by
  intro p hp
  letI : Fact p.Prime := ⟨hS p hp⟩
  exact ⟨selectedPrimeOver K p, selectedPrimeOver_mem K p⟩

/-- The chosen prime-ideal product over a finite rational support. -/
noncomputable def selectedIdealProduct
    (S : Finset Nat) (hS : ∀ p ∈ S, Nat.Prime p) :
    Ideal (NumberField.RingOfIntegers K) :=
  S.attach.prod (fun p =>
    letI : Fact p.1.Prime := ⟨hS p.1 p.2⟩
    selectedPrimeOver K p.1)

#check selectedPrimeOver
#check selectedPrimeOver_mem
#check exists_primeOver_of_mem_support
#check selectedIdealProduct
#print axioms exists_primeOver_of_mem_support

end LeanFormal.IUT.XiFPaper.S2738PrimeOverSelectionActual
end
