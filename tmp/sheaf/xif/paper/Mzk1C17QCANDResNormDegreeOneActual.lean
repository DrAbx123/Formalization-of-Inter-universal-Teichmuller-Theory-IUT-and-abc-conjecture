/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17QCANDOrderResidueActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import Mathlib.Tactic

/-! # P6-E2: RESNORM from local residue degree one (single cluster, CONDITIONAL) -/
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderResidueActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
namespace LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormDegreeOneActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem resNorm_eq_of_localResidueDegree_one
    (hK : localResidueDegree (k := T.arithmetic.Fmod)
      (nativeBaseSectionPlace T b) = 1)
    (hF : localResidueDegree (k := T.arithmetic.Fmod)
      (qVFamTensorPlace T b) = 1) :
    residueNormBase (nativeBaseSectionPlace T b) =
      residueNormBase (qVFamTensorPlace T b) := by
  rw [residueNormBase_eq_lower_pow (k := T.arithmetic.Fmod)
      (nativeBaseSectionPlace T b),
    residueNormBase_eq_lower_pow (k := T.arithmetic.Fmod)
      (qVFamTensorPlace T b)]
  simp only [nativeBaseSectionPlace_comap, (nativeBadLift T).lift_comap, hK, hF, pow_one]

theorem qcandResNormGap_of_localResidueDegree_one
    (hK : ∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod)
        (nativeBaseSectionPlace T b) = 1)
    (hF : ∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod)
        (qVFamTensorPlace T b) = 1) :
    QCANDResNormGap T := by
  intro b
  exact resNorm_eq_of_localResidueDegree_one T b (hK b) (hF b)

def resNormDegreeOneRows : List (String × String × String) :=
  [ ("resNorm_eq_of_localResidueDegree_one", "f=1 at both places => residue equality", "PROVED conditional"),
    ("qcandResNormGap_of_localResidueDegree_one", "pointwise f=1 => RESNORM", "PROVED conditional") ]
theorem resNormDegreeOneRows_length : resNormDegreeOneRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormDegreeOneActual

-- retry marker after compile-fix batch
