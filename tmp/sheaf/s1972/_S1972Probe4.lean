import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import tmp.sheaf.xif.paper.S1964QuotientCFActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual

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

theorem honestCKTors_euler (l : PrimeGeFive) :
    (honestCKTors l).eulerCharacteristic = -(l.value : ℚ) / 2 := by
  have hodd : Odd l.value := l.odd
  rcases hodd with ⟨m, hm⟩
  have hdiv : (l.value + 1) / 2 = m + 1 := by omega
  simp only [honestCKTors, Iut.OrbicurveSignature.eulerCharacteristic]
  norm_num
  rw [hdiv]
  rw [hm]
  norm_num
  ring

theorem honestCKTors_hyperbolic (l : PrimeGeFive) :
    (honestCKTors l).IsHyperbolic := by
  rw [Iut.OrbicurveSignature.IsHyperbolic, honestCKTors_euler]
  have h5 : (5 : ℚ) ≤ (l.value : ℚ) := by
    have := l.ge_five
    exact_mod_cast this
  linarith

def toIutSignature (s : SourceOrbicurveSignature) : Iut.OrbicurveSignature where
  genus := s.genus
  stackyOrders := s.stackyOrders
  punctures := s.punctures
  stackyOrders_ge_two := s.stackyOrders_ge_two

example : toIutSignature SourceOrbicurveSignature.typeOneOne ≠ S1964HonestQuotientSignature := by
  intro h
  have hg := congrArg Iut.OrbicurveSignature.genus h
  rw [show (toIutSignature SourceOrbicurveSignature.typeOneOne).genus = 1 from rfl,
      show S1964HonestQuotientSignature.genus = 0 from rfl] at hg
  exact Nat.one_ne_zero hg

example (l : PrimeGeFive) :
    toIutSignature (SourceOrbicurveSignature.typeOneLTorsion l) ≠ honestXKTors l := by
  intro h
  have hp := congrArg Iut.OrbicurveSignature.punctures h
  rw [show (toIutSignature (SourceOrbicurveSignature.typeOneLTorsion l)).punctures = 0 from rfl,
      show (honestXKTors l).punctures = l.value from rfl] at hp
  have h5 := l.ge_five
  omega

example (l : PrimeGeFive) :
    toIutSignature (SourceOrbicurveSignature.typeOneLTorsionPlusMinus l) ≠ honestCKTors l := by
  intro h
  have hg := congrArg Iut.OrbicurveSignature.genus h
  rw [show (toIutSignature (SourceOrbicurveSignature.typeOneLTorsionPlusMinus l)).genus = 1 from rfl,
      show (honestCKTors l).genus = 0 from rfl] at hg
  exact Nat.one_ne_zero hg

end Scratch
