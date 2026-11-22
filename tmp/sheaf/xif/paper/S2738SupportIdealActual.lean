import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalBoundaryPrimeSupport
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import Mathlib.RingTheory.Ideal.Int

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2738SupportIdealActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle

universe u
variable {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)

abbrev O (A : InitialThetaArithmeticData.{u} l) : Type u :=
  NumberField.RingOfIntegers A.K

noncomputable def supportPrimeIdeal (a c : Nat) (p : Nat)
    (hp : p ∈ arithmeticPrimeSupport (abcRationalPoint a c)) : Ideal (O A) := by
  haveI : Fact (Nat.Prime p) :=
    ⟨prime_of_mem_arithmeticPrimeSupport (x := abcRationalPoint a c) hp⟩
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime p
  exact Classical.choose
    (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (R := ℤ) (S := O A) (Ideal.span {(p : ℤ)}))

noncomputable def supportIdeal (a c : Nat) : Ideal (O A) :=
  Finset.prod (arithmeticPrimeSupport (abcRationalPoint a c)).attach
    (fun p => supportPrimeIdeal (A := A) a c p.1 p.2)

theorem supportIdeal_ne_bot (a c : Nat) : supportIdeal (A := A) a c ≠ ⊥ := by
  rw [supportIdeal]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro p hp
  haveI : Fact (Nat.Prime p) :=
    ⟨prime_of_mem_arithmeticPrimeSupport (x := abcRationalPoint a c) p.2⟩
  haveI : Fact (Nat.Prime (p : Nat)) :=
  haveI : (Ideal.span {((p : Nat) : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime (p : Nat)
    (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (R := ℤ) (S := O A) (Ideal.span {((p : Nat) : ℤ)}))
  exact Ring.ne_bot_of_isMaximal_of_not_isField h.1
    (NumberField.RingOfIntegers.not_isField A.K)

#check supportPrimeIdeal
#check supportIdeal
#check supportIdeal_ne_bot

end LeanFormal.IUT.XiFPaper.S2738SupportIdealActual
end
