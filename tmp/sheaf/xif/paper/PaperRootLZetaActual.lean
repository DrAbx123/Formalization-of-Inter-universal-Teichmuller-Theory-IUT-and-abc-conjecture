import tmp.sheaf.xif.paper.PaperRootLValuedTensorCarrierActual
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

-- S231: LZeta rebuilt over the finite complete RootL = rootNormedExtension.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperRootLZetaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def rootLZeta : rootNormedAmbient T b :=
  Classical.choose (HasEnoughRootsOfUnity.exists_primitiveRoot
    (rootNormedAmbient T b) (2 * l.value))

theorem rootLZeta_pow :
    rootLZeta T b ^ (2 * l.value) = 1 :=
  (Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot
    (rootNormedAmbient T b) (2 * l.value))).pow_eq_one

theorem rootLZeta_ne_zero : rootLZeta T b ≠ 0 := by
  intro h
  have hp := rootLZeta_pow T b
  rw [h] at hp
  have hpos : 2 * l.value ≠ 0 := Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  rw [zero_pow hpos] at hp
  exact zero_ne_one hp

theorem rootLZeta_isIntegral :
    IsIntegral (RootL T b) (rootLZeta T b) := by
  have hpow : IsIntegral (RootL T b) ((rootLZeta T b) ^ (2 * l.value)) := by
    rw [rootLZeta_pow]
    exact isIntegral_algebraMap
  exact IsIntegral.of_pow (by
    exact Nat.mul_pos (by norm_num) l.prime.pos) hpow

abbrev RootLZetaField : IntermediateField (RootL T b) (rootNormedAmbient T b) :=
  IntermediateField.adjoin (RootL T b) ({rootLZeta T b} : Set (rootNormedAmbient T b))

abbrev RootLZeta : Type := RootLZetaField T b

instance rootLZetaField : Field (RootLZeta T b) := inferInstance

noncomputable instance rootLZetaNormedField : NormedField (RootLZeta T b) := inferInstance

noncomputable instance rootLZetaFiniteDimensional :
    FiniteDimensional (RootL T b) (RootLZeta T b) :=
  IntermediateField.adjoin.finiteDimensional
    (K := RootL T b) (x := rootLZeta T b) (rootLZeta_isIntegral T b)

noncomputable instance rootLZetaCompleteSpace : CompleteSpace (RootLZeta T b) := by
  haveI : FiniteDimensional (RootL T b) (RootLZeta T b) := rootLZetaFiniteDimensional T b
  exact FiniteDimensional.complete (RootL T b) (RootLZeta T b)

noncomputable instance rootLZetaProperSpace : ProperSpace (RootLZeta T b) := by
  exact @FiniteDimensional.proper (RootL T b) inferInstance (RootLZeta T b)
    inferInstance inferInstance inferInstance (rootLZetaFiniteDimensional T b)

noncomputable instance rootLZetaMeasurableSpace : MeasurableSpace (RootLZeta T b) := borel _

#check rootLZeta
#check RootLZeta
#check rootLZetaFiniteDimensional
#check rootLZetaCompleteSpace
#check rootLZetaProperSpace

end LeanFormal.IUT.XiFPaper.PaperRootLZetaActual

end