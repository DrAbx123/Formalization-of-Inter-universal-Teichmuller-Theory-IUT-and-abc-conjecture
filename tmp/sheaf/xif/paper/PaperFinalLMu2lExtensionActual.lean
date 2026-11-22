import tmp.sheaf.xif.paper.PaperFinalLValuedTensorCarrierActual
import tmp.sheaf.xif.paper.PaperC3PrimitiveMu2lRootActual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

-- S208: actual primitive mu_{2l} root inside L, the minimal extension L(zeta),
-- and the actual mu_{2l} action on the FinalLValued tensor carrier.
-- No inequality.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperFinalLMu2lExtensionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperC3PrimitiveMu2lRootActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaValuesActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open scoped TensorProduct

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def finalLPrimitiveMu2lRoot :
    PrimitiveMu2lRoot (finalLGeometry T b) PUnit.unit :=
  primitiveMu2lRoot (finalLGeometry T b) PUnit.unit

noncomputable def finalLZeta : FinalL T b :=
  (finalLPrimitiveMu2lRoot T b).zeta

theorem finalLZeta_pow : finalLZeta T b ^ (2 * l.value) = 1 :=
  (finalLPrimitiveMu2lRoot T b).zeta_pow

theorem finalLZeta_ne_zero : finalLZeta T b ≠ 0 := by
  intro h
  have hp := finalLZeta_pow T b
  rw [h] at hp
  have hpos : 2 * l.value ≠ 0 := Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  rw [zero_pow hpos] at hp
  exact zero_ne_one hp

-- Minimal extension L(zeta) inside L; field structure is actual.
abbrev LZetaField : IntermediateField (FinalL T b) (FinalL T b) :=
  IntermediateField.adjoin (FinalL T b)
    ({finalLZeta T b} : Set (FinalL T b))

abbrev LZeta : Type := LZetaField T b

instance lZetaField : Field (LZeta T b) := inferInstance

theorem lZeta_contains_zeta :
    finalLZeta T b ∈ (LZetaField T b : Set (FinalL T b)) :=
  IntermediateField.subset_adjoin _ _ (by simp)

noncomputable def finalLZetaUnit (m : Nat) : (FinalL T b)ˣ :=
  Units.mk0 (finalLZeta T b ^ m)
    (pow_ne_zero m (finalLZeta_ne_zero T b))

-- Actual mu_{2l} action on the L-valued tensor carrier: scaling the L
-- component by zeta^m.
noncomputable def finalLMu2lAction (m : Nat) :
    FinalLValuedCarrier T b ≃ₗ[ℚ_[qVFamTensorP T b]]
      FinalLValuedCarrier T b :=
  TensorProduct.congr (LinearEquiv.refl _ _)
    (finalLUnitMulEquiv (l := l) T b (finalLZetaUnit T b m))

-- Exact normed-field gap on L(zeta): field structure is actual; no
-- NormedField/CompleteSpace instance is faked.
structure LZetaNormedGap where
  normedField : NormedField (LZeta T b)
  completeSpace : CompleteSpace (LZeta T b)
  measurableSpace : MeasurableSpace (LZeta T b)

def LZetaNormedGapRequired : Prop :=
  Nonempty (LZetaNormedGap T b)

#check finalLPrimitiveMu2lRoot
#check finalLZeta
#check LZeta
#check lZeta_contains_zeta
#check finalLMu2lAction
#check LZetaNormedGap

end LeanFormal.IUT.XiFPaper.PaperFinalLMu2lExtensionActual

end