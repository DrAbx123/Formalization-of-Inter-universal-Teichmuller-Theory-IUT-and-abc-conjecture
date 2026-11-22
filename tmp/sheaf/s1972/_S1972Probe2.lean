import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace Scratch

def honestXKTors (l : PrimeGeFive) : Iut.OrbicurveSignature where
  genus := 1
  stackyOrders := []
  punctures := l.value
  stackyOrders_ge_two := by simp

def honestCKTors (l : PrimeGeFive) : Iut.OrbicurveSignature where
  genus := 0
  stackyOrders := [2, 2, 2]
  punctures := (l.value + 1) / 2
  stackyOrders_ge_two := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide

theorem honestXKTors_euler (l : PrimeGeFive) :
    (honestXKTors l).eulerCharacteristic = -(l.value : ℚ) := by
  norm_num [honestXKTors, Iut.OrbicurveSignature.eulerCharacteristic]

theorem honestCKTors_euler_lt (l : PrimeGeFive) :
    (honestCKTors l).eulerCharacteristic ≤ -(5 : ℚ) / 2 := by
  have h5 : 5 ≤ l.value := l.ge_five
  have h3 : (3 : ℚ) ≤ ((l.value + 1) / 2 : ℕ) := by
    have h : (3 : ℕ) ≤ (l.value + 1) / 2 := by omega
    exact_mod_cast h
  simp only [honestCKTors, Iut.OrbicurveSignature.eulerCharacteristic]
  norm_num
  linarith

theorem honestXKTors_hyperbolic (l : PrimeGeFive) :
    (honestXKTors l).IsHyperbolic := by
  rw [Iut.OrbicurveSignature.IsHyperbolic, honestXKTors_euler]
  have h5 : (5 : ℚ) ≤ (l.value : ℚ) := by
    have : 5 ≤ l.value := l.ge_five
    exact_mod_cast this
  linarith

theorem honestCKTors_hyperbolic (l : PrimeGeFive) :
    (honestCKTors l).IsHyperbolic := by
  rw [Iut.OrbicurveSignature.IsHyperbolic]
  have h := honestCKTors_euler_lt l
  linarith

end Scratch
