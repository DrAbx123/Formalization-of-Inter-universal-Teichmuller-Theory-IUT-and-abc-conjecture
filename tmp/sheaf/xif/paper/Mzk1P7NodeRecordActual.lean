/- P7 native node record: Clause C support, full SL2 large image, gap nonneg
and gap add for the reconstructed native source. -/
import tmp.sheaf.xif.paper.Mzk1P7NodeAssemblyDoneActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P7NodeRecordActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1P7NodeAssemblyDoneActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]
variable [∀ b : Bad (nativePlaceSelection X.S), MeasurableSpace (qVFamTensorBlock X.S b)]
variable [∀ b : Bad (nativePlaceSelection X.S), BorelSpace (qVFamTensorBlock X.S b)]

theorem p7Node_clauseC_support :
    Mzk1P7ClauseCSupportActual.P7ClauseCSupport (l := l)
      (Mzk1P7SourceTorsionDatumActual.sourceClauseC_of_native X) :=
  (p7_native_node_assembly X).1

theorem p7Node_largeImage :
    ∀ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value),
      M.toGL ∈ (X.S.arithmetic.curve.galoisLTorsionMatrixRepresentation
        l (Mzk1P7SourceTorsionDatumActual.sourceClauseC_of_native X).torsion_basis).range :=
  (p7_native_node_assembly X).2.1

theorem p7Node_gap_nonneg :
    0 ≤ LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual.qVFamThetaReading X -
      LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X :=
  (p7_native_node_assembly X).2.2.1
#print axioms p7Node_clauseC_support
#print axioms p7Node_gap_nonneg
end LeanFormal.IUT.XiFPaper.Mzk1P7NodeRecordActual
end
