import tmp.sheaf.xif.paper.S2703GaussianPrimePlacesActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
set_option maxRecDepth 100000
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2703GaussianPrimePlacesActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.ArithmeticQPilotBaseChange

namespace LeanFormal.IUT.XiFPaper.S2707ResidueNormDegreeOneActual

local instance s2707GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem gaussianField2161PrimePlus_absNorm :
    (gaussianField2161PrimePlus).absNorm = 2161 := by
  rw [Ideal.absNorm_apply]
  change Submodule.cardQuot gaussianField2161PrimePlus = 2161
  rw [Submodule.cardQuot_apply]
  calc Nat.card (gaussianO ⧸ gaussianField2161PrimePlus)
      = Nat.card (ZMod 2161) :=
        Nat.card_congr gaussianField2161PrimePlusResidueEquiv.toEquiv
    _ = 2161 := Nat.card_zmod 2161

theorem gaussianField2161PrimeMinus_absNorm :
    (gaussianField2161PrimeMinus).absNorm = 2161 := by
  rw [Ideal.absNorm_apply]
  change Submodule.cardQuot gaussianField2161PrimeMinus = 2161
  rw [Submodule.cardQuot_apply]
  calc Nat.card (gaussianO ⧸ gaussianField2161PrimeMinus)
      = Nat.card (ZMod 2161) :=
        Nat.card_congr gaussianField2161PrimeMinusResidueEquiv.toEquiv
    _ = 2161 := Nat.card_zmod 2161

theorem S2707_fivePlus :
    residueNormBase gaussianPlaceFivePlus =
      (NumberFieldFinitePlace.residueCharacteristic gaussianPlaceFivePlus : ℝ) := by
  unfold residueNormBase
  rw [gaussianPlaceFivePlus_maximalIdeal]
  change (Ideal.absNorm gaussianFieldFivePrimePlus : ℝ) =
    (NumberFieldFinitePlace.residueCharacteristic gaussianPlaceFivePlus : ℝ)
  rw [gaussianFieldFivePrimePlus_absNorm, gaussianPlaceFivePlus_residueCharacteristic]

theorem S2707_fiveMinus :
    residueNormBase gaussianPlaceFiveMinus =
      (NumberFieldFinitePlace.residueCharacteristic gaussianPlaceFiveMinus : ℝ) := by
  unfold residueNormBase
  rw [gaussianPlaceFiveMinus_maximalIdeal]
  change (Ideal.absNorm gaussianFieldFivePrimeMinus : ℝ) =
    (NumberFieldFinitePlace.residueCharacteristic gaussianPlaceFiveMinus : ℝ)
  rw [gaussianFieldFivePrimeMinus_absNorm, gaussianPlaceFiveMinus_residueCharacteristic]

theorem S2707_2161Plus :
    residueNormBase gaussianPlace2161Plus =
      (NumberFieldFinitePlace.residueCharacteristic gaussianPlace2161Plus : ℝ) := by
  unfold residueNormBase
  rw [gaussianPlace2161Plus_maximalIdeal]
  change (Ideal.absNorm gaussianField2161PrimePlus : ℝ) =
    (NumberFieldFinitePlace.residueCharacteristic gaussianPlace2161Plus : ℝ)
  rw [gaussianField2161PrimePlus_absNorm, gaussianPlace2161Plus_residueCharacteristic]

theorem S2707_2161Minus :
    residueNormBase gaussianPlace2161Minus =
      (NumberFieldFinitePlace.residueCharacteristic gaussianPlace2161Minus : ℝ) := by
  unfold residueNormBase
  rw [gaussianPlace2161Minus_maximalIdeal]
  change (Ideal.absNorm gaussianField2161PrimeMinus : ℝ) =
    (NumberFieldFinitePlace.residueCharacteristic gaussianPlace2161Minus : ℝ)
  rw [gaussianField2161PrimeMinus_absNorm, gaussianPlace2161Minus_residueCharacteristic]

#check S2707_fivePlus
#check S2707_fiveMinus
#check S2707_2161Plus
#check S2707_2161Minus
#print axioms S2707_fivePlus
#print axioms S2707_fiveMinus
#print axioms S2707_2161Plus
#print axioms S2707_2161Minus

end LeanFormal.IUT.XiFPaper.S2707ResidueNormDegreeOneActual
end
