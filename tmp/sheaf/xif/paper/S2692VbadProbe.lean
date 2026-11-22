import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegreeGlobal
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2692VbadProbe

local instance s2692GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

def S2692Prime2161 : Nat.Primes := ⟨2161, by norm_num⟩

def S2692HeightOne2161 :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
    S2692Prime2161

def S2692Place2161 : NumberField.FinitePlace ℚ :=
  NumberField.FinitePlace.mk S2692HeightOne2161

theorem S2692HeightOne2161_natGenerator :
    Rat.HeightOneSpectrum.natGenerator S2692HeightOne2161 = 2161 := by
  exact congrArg (fun p : Nat.Primes => p.1)
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := NumberField.RingOfIntegers ℚ)).apply_symm_apply S2692Prime2161)

noncomputable def S2692GaussianPlace2161 : NumberField.FinitePlace GaussianField :=
  Classical.choose
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := GaussianField) S2692Place2161)

theorem S2692GaussianPlace2161_comap :
    NumberFieldFinitePlace.comap (k := ℚ) S2692GaussianPlace2161 =
      S2692Place2161 :=
  Classical.choose_spec
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := GaussianField) S2692Place2161)

theorem S2692Place2161_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic S2692Place2161 = 2161 := by
  unfold NumberFieldFinitePlace.residueCharacteristic NumberFieldFinitePlace.ResidueField
  rw [S2692Place2161, NumberField.FinitePlace.maximalIdeal_mk]
  rw [S2692HeightOne2161_natGenerator]
  norm_num

#check S2692Place2161_residueCharacteristic
#check S2692GaussianPlace2161
end LeanFormal.IUT.XiFPaper.S2692VbadProbe
end
