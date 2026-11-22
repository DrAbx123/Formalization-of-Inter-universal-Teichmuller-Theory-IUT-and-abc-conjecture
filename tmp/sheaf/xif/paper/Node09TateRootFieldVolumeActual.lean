import tmp.sheaf.xif.paper.Mzk1P1RootRadiusBridgeActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.Mzk1P1RootRadiusBridgeActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.S305SingleLambdaNormActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual

namespace LeanFormal.IUT.XiFPaper.Node09TateRootFieldVolumeActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- P1 volume/root-field formula (R): the actual root-field normalized log-volume
equals (1/(2l)) log ||q||.  Here rootNormedExtension is the actual finite root
field L/F and rootNormedLogVolume is its (already normalized) log-volume. -/
theorem p1_rootFieldVolume_formula :
    rootNormedLogVolume (l := l) T b =
      (1 / (2 * (l.value : Real))) *
        Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ :=
  rootNormedLogVolume_eq_inv_twoL_mul_log_norm (T := T) b

/-- The root field is a finite extension of the base local field. -/
theorem p1_rootField_finiteDimensional :
    FiniteDimensional (rootBase (l := l) T b) (rootNormedExtension (l := l) T b) :=
  inferInstance

/-- The root-field log-volume is the log norm of the actual root unit in L. -/
theorem p1_rootFieldLogVolume_eq_rootUnit :
    rootNormedLogVolume (l := l) T b =
      Real.log ‖(rootNormedUnit (l := l) T b : rootNormedExtension (l := l) T b)‖ := rfl

def Node09P1RootFieldVolumeStatus : List String :=
  [ "actual: p1_rootFieldVolume_formula is the (R) formula rootNormedLogVolume = (1/(2l)) log||q|| (donor Mzk1P1RootRadiusBridgeActual.rootNormedLogVolume_eq_inv_twoL_mul_log_norm)",
    "actual: rootNormedExtension is finite over rootBase and rootNormedLogVolume is the normalized log volume of the actual root unit",
    "root-to-K_v 2l-torsion rationality is not needed for the volume-only branch; left to P3",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateRootFieldVolumeActual