import tmp.sheaf.xif.paper.Mzk1P7SourceTorsionDatumActual
import tmp.sheaf.xif.paper.Mzk1P7ClauseCSupportActual
import tmp.sheaf.xif.paper.Mzk1P7LargeImageSourceDoneActual
import tmp.sheaf.xif.paper.Mzk1P7GapActualActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Mzk1P7SourceTorsionDatumActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ClauseCSupportActual
open LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageSourceDoneActual
open LeanFormal.IUT.XiFPaper.Mzk1P7GapActualActual

namespace LeanFormal.IUT.XiFPaper.Mzk1P7NodeAssemblyActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- P7 node assembly: native Clause C support, full SL2 large-image, and the
actual P5 gap inequality, all for the same native input. -/
theorem p7_native_node_assembly
    (hMeas : ∀ b : Bad (nativePlaceSelection X.S), MeasurableSpace (qVFamTensorBlock X.S b))
    (hBorel : ∀ b : Bad (nativePlaceSelection X.S), BorelSpace (qVFamTensorBlock X.S b)) :
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
  · exact @LeanFormal.IUT.XiFPaper.Mzk1P7GapActualActual.p7_gap_nonneg_actual l X
      (inferInstance : Fintype (Bad (nativePlaceSelection X.S))) hMeas hBorel
  · exact LeanFormal.IUT.XiFPaper.Mzk1P7GapActualActual.p7_gap_add_actual X

#print axioms p7_native_node_assembly
end LeanFormal.IUT.XiFPaper.Mzk1P7NodeAssemblyActual