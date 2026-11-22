/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17QCANDOrderResidueActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import Mathlib.Tactic

/-! # P6-D3: QCAND RESNORM via comap/residue degree (single cluster) -/
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
namespace LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem log_residue_sectionK_eq_degree_mul :
    Real.log (residueNormBase (nativeBaseSectionPlace T b)) =
      (localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) : Real) *
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (nativeBaseSectionPlace T b))) :=
  log_residueNormBase_eq_residueDegree_mul
    (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b)

theorem log_residue_nativeF_eq_degree_mul :
    Real.log (residueNormBase (qVFamTensorPlace T b)) =
      (localResidueDegree (k := T.arithmetic.Fmod) (qVFamTensorPlace T b) : Real) *
        Real.log (residueNormBase (comap (k := T.arithmetic.Fmod)
          (qVFamTensorPlace T b))) :=
  log_residueNormBase_eq_residueDegree_mul
    (k := T.arithmetic.Fmod) (qVFamTensorPlace T b)

/-- The remaining RESNORM content: same residue degree at the two places. -/
def ResNormDegreeGap : Prop :=
  forall b : Bad (nativePlaceSelection T),
    localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) =
      localResidueDegree (k := T.arithmetic.Fmod) (qVFamTensorPlace T b)

def resNormComapRows : List (String × String × String) :=
  [ ("log_residue_sectionK_eq_degree_mul", "log residue K = f_K * log lower", "PROVED"),
    ("log_residue_nativeF_eq_degree_mul", "log residue F = f_F * log lower", "PROVED"),
    ("ResNormDegreeGap", "f_K = f_F per b", "GAP (Prop)") ]
theorem resNormComapRows_length : resNormComapRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
