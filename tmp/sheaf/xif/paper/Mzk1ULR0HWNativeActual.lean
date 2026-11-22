/- R0-c/hW q-side: nativeBadLocalWeight_b * cNorm_b = (1/(2l)) * cPFullFiber_b.
   The absolute e is counted ONCE: cNorm = order/e_abs is the paper cP (S826 norm-compat
   case, encoded as hC). No [K_w:F_P] reduction is used. The remaining hW content is the
   weight identity nativeBadLocalWeight_b = thetaLamWeight_b/(2l) plus R0-b crosswalk. -/
import tmp.sheaf.xif.paper.Mzk1ULR0FiberCrosswalkActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR0HWNativeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0FiberCrosswalkActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR0RealDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR1MpaperBWeightActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- hW q-side: with cNorm = paper cP, native weight = thetaLamWeight/(2l), and R0-b
    crosswalk, the native q coefficient equals (1/(2l)) * cPFullFiber. -/
theorem hW_native_of_weight_identity
    (hC : ∀ b : Bad (nativePlaceSelection T),
      QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b = cP (l := l) T b)
    (hW : ∀ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b = thetaLamWeight T b / (2 * (l.value : Real)))
    (hcross : ∀ b : Bad (nativePlaceSelection T),
      cPFullFiber (l := l) T b = thetaLamWeight T b * cP (l := l) T b) :
    ∀ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b *
        QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b =
      (1 / (2 * (l.value : Real))) * cPFullFiber (l := l) T b := by
  intro b
  have hl : (2 * (l.value : Real)) ≠ 0 := by
    have h : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
    positivity
  rw [hC b, hW b, hcross b]
  field_simp [hl]
  ring

#print axioms hW_native_of_weight_identity

end LeanFormal.IUT.XiFPaper.Mzk1ULR0HWNativeActual
