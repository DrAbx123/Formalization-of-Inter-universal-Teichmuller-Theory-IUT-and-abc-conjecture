import tmp.sheaf.xif.paper.S2738PrimeOverFamilyActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalBoundaryPrimeSupport
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2739SupportIdealActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2738PrimeOverFamilyActual
open LeanFormal.IUT.XiFPaperArithmeticLineBundle

universe u
variable {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)

abbrev SupportIndex (a c : Nat) : Type :=
  {p : Nat // p ∈ arithmeticPrimeSupport (abcRationalPoint a c)}

noncomputable def supportIndexFintype (a c : Nat) : Fintype (SupportIndex a c) :=
  Fintype.ofFinset (arithmeticPrimeSupport (abcRationalPoint a c)) (fun p => Iff.rfl)

noncomputable def supportRationalPlace (a c : Nat) (p : SupportIndex a c) :
    NumberField.FinitePlace ℚ := by
  haveI : Fact (Nat.Prime p.1) :=
    ⟨prime_of_mem_arithmeticPrimeSupport (x := abcRationalPoint a c) p.2⟩
  exact rationalFinitePlace p.1

noncomputable def supportPlaceFamily (a c : Nat) :
    SupportIndex a c → NumberField.FinitePlace A.K :=
  Classical.choose (S2738_exists_place_family_over
    (K := A.K) (supportRationalPlace a c))

theorem supportPlaceFamily_comap (a c : Nat) (p : SupportIndex a c) :
    comap (k := ℚ) (supportPlaceFamily a c p) =
      supportRationalPlace a c p :=
  Classical.choose_spec (S2738_exists_place_family_over
    (K := A.K) (supportRationalPlace a c)) p

noncomputable def supportIdeal (a c : Nat) :
    Ideal (NumberField.RingOfIntegers A.K) := by
  letI := supportIndexFintype a c
  exact S2738PrimeProduct (K := A.K) (supportPlaceFamily a c)

theorem supportIdeal_absNorm (a c : Nat) :
    Ideal.absNorm (supportIdeal (A := A) a c) =
      ∏ p : SupportIndex a c,
        Ideal.absNorm ((supportPlaceFamily a c p).maximalIdeal.asIdeal) := by
  letI := supportIndexFintype a c
  exact S2738_absNorm_primeProduct (K := A.K)
    (supportPlaceFamily a c)

#check SupportIndex
#check supportRationalPlace
#check supportPlaceFamily
#check supportIdeal
#check supportIdeal_absNorm

end LeanFormal.IUT.XiFPaper.S2739SupportIdealActualAdapted
end
