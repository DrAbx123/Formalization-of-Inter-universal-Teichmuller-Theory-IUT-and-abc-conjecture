import tmp.sheaf.xif.paper.Mzk1P7NativeSourceActual
import tmp.sheaf.xif.paper.Mzk1P7GapActualActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.Node09P5ThetaSideFinalActual
import tmp.sheaf.xif.paper.S3133RealifiedQPilotLogVolumeActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P7SourceTorsionDatumActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ClauseCSupportActual
open LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageSourceDoneActual
open LeanFormal.IUT.XiFPaper.Mzk1P7GapActualActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P7NodeAssemblyDoneActual
variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]
variable [∀ b : Bad (nativePlaceSelection X.S), MeasurableSpace (qVFamTensorBlock X.S b)]
variable [∀ b : Bad (nativePlaceSelection X.S), BorelSpace (qVFamTensorBlock X.S b)]
/-- P7 node assembly: native Clause C support, full SL2 large-image, and the
actual P5 gap inequality for the same native input. -/
theorem p7_native_node_assembly :
    P7ClauseCSupport (l := l) (sourceClauseC_of_native X) ∧
    (∀ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value),
      M.toGL ∈ (X.S.arithmetic.curve.galoisLTorsionMatrixRepresentation
        l (sourceClauseC_of_native X).torsion_basis).range) ∧
    0 ≤ LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual.qVFamThetaReading X -
      LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X ∧
    LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X +
      (LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual.qVFamThetaReading X -
        LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X) =
      LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual.qVFamThetaReading X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact p7_clauseC_support (sourceClauseC_of_native X)
  · exact p7_D_largeImage_source (sourceClauseC_of_native X)
  · exact p7_gap_nonneg_actual X
  · exact p7_gap_add_actual X
#print axioms p7_native_node_assembly
end LeanFormal.IUT.XiFPaper.Mzk1P7NodeAssemblyDoneActual
end