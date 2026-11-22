import tmp.sheaf.xif.paper.S2700FivePlaceComapBridgeActual
import tmp.sheaf.xif.paper.S2709ResidueNormCharActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2699TwoFivePlacesActual
open LeanFormal.IUT.XiFPaper.S2700FivePlaceComapBridgeActual
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2710FiveResidueNormDegreeActual

local instance s2710FiveFact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
local instance s2710GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2710AbsNormPlus :
    Ideal.absNorm gaussianFieldFivePrimePlus = 5 :=
  gaussianFieldFivePrimePlus_absNorm

theorem S2710AbsNormMinus :
    Ideal.absNorm gaussianFieldFivePrimeMinus = 5 :=
  gaussianFieldFivePrimeMinus_absNorm

theorem S2710AbsNormBaseFive :
    Ideal.absNorm (concreteFivePlace.maximalIdeal.asIdeal) = 5 := by
  rw [concreteFivePlace_maximalIdeal, concreteFiveHeightOne_asIdeal_eq_span]
  exact gaussianRationalFive_absNorm

theorem S2710RelativeResidueDegreePlus :
    relativeResidueDegree (k := ℚ) S2699GaussianPlaceFivePlus = 1 := by
  have h := absNorm_eq_pow_relativeResidueDegree (k := ℚ) S2699GaussianPlaceFivePlus
  have hupper :
      Ideal.absNorm S2699GaussianPlaceFivePlus.maximalIdeal.asIdeal = 5 := by
    rw [S2699PlaceFivePlus_maximalIdeal]
    exact S2710AbsNormPlus
  rw [S2700ComapPlus, hupper, S2710AbsNormBaseFive] at h
  have hinj : Function.Injective (fun n : Nat => (5 : Real) ^ n) :=
    pow_right_injective₀ (by norm_num) (by norm_num)
  apply hinj
  calc
    (5 : Real) ^ relativeResidueDegree (k := ℚ) S2699GaussianPlaceFivePlus = 5 :=
      h.symm
    _ = (5 : Real) ^ 1 := by norm_num

theorem S2710RelativeResidueDegreeMinus :
    relativeResidueDegree (k := ℚ) S2699GaussianPlaceFiveMinus = 1 := by
  have h := absNorm_eq_pow_relativeResidueDegree (k := ℚ) S2699GaussianPlaceFiveMinus
  have hupper :
      Ideal.absNorm S2699GaussianPlaceFiveMinus.maximalIdeal.asIdeal = 5 := by
    rw [S2699PlaceFiveMinus_maximalIdeal]
    exact S2710AbsNormMinus
  rw [S2700ComapMinus, hupper, S2710AbsNormBaseFive] at h
  have hinj : Function.Injective (fun n : Nat => (5 : Real) ^ n) :=
    pow_right_injective₀ (by norm_num) (by norm_num)
  apply hinj
  calc
    (5 : Real) ^ relativeResidueDegree (k := ℚ) S2699GaussianPlaceFiveMinus = 5 :=
      h.symm
    _ = (5 : Real) ^ 1 := by norm_num

#print axioms S2710AbsNormPlus
#print axioms S2710RelativeResidueDegreePlus

end LeanFormal.IUT.XiFPaper.S2710FiveResidueNormDegreeActual
end
