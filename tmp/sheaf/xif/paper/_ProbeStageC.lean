import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.Foundations.Geometry.FinitePlaceDegreeSumBound
import Mathlib.NumberTheory.RamificationInertia.Basic

noncomputable section
open LeanFormal.IUT
namespace ProbeStageC

open LeanFormal.IUT.InitialThetaSource
def eSet (K : Type*) [Field K] [NumberField K] : Set ℕ :=
  {e | ∃ p : NumberField.FinitePlace K, p.maximalIdeal.asIdeal.ramificationIdx ℤ = e}

noncomputable def eModNat (K : Type*) [Field K] [NumberField K] : ℕ := by
  classical
  exact Nat.findGreatest (fun e => e ∈ eSet K) (Module.finrank ℚ K)

theorem ramIdx_le_finrank (K : Type*) [Field K] [NumberField K]
    (p : NumberField.FinitePlace K) :
    p.maximalIdeal.asIdeal.ramificationIdx ℤ ≤ Module.finrank ℚ K := by
  haveI : p.maximalIdeal.asIdeal.LiesOver
      (Ideal.span {(NumberFieldFinitePlace.residueCharacteristic p : ℤ)}) := by
    rw [Ideal.liesOver_iff]
    exact (NumberFieldFinitePlace.under_eq_span_residueCharacteristic p).symm
  haveI : Fact (Nat.Prime (NumberFieldFinitePlace.residueCharacteristic p)) :=
    ⟨NumberFieldFinitePlace.residueCharacteristic_prime p⟩
  haveI : (Ideal.span {(NumberFieldFinitePlace.residueCharacteristic p : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime (NumberFieldFinitePlace.residueCharacteristic p)
  exact Ideal.ramificationIdx_le_finrank (R := ℤ) (S := NumberField.RingOfIntegers K)
    (K := ℚ) (L := K) (p := Ideal.span {(NumberFieldFinitePlace.residueCharacteristic p : ℤ)})
    (P := p.maximalIdeal.asIdeal)

example (K : Type*) [Field K] [NumberField K] :
    eModNat K ≤ Module.finrank ℚ K := by
  unfold eModNat
  exact @Nat.findGreatest_le (fun e => e ∈ eSet K) (Classical.decPred _) _

end ProbeStageC
end
