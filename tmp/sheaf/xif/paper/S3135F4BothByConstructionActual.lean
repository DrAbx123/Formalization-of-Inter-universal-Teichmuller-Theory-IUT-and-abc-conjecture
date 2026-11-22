import tmp.sheaf.xif.paper.S3135ModelF4aTemplateActual
import tmp.sheaf.xif.paper.S3135RealifiedIdentificationActual
import tmp.sheaf.xif.paper.S3135ProcessionUnitDatumActual

noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.S3135ValueGroupDegreeUnconditionalActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual
open LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.XiFPaper.S3135RealifiedIdentActual
open LeanFormal.IUT.XiFPaper.S3135ProcessionDatumActual
open LeanFormal.IUT.XiFPaper.S3135ModelF4aBatchActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput

namespace LeanFormal.IUT.XiFPaper.S3135F4BothByConstructionActual

/-- **F4 (a)+(b) closed from the two corpus class-B data** (the transfer to the model
route is by construction: in the model both data are definitional/choice). -/
theorem s3135_actualF4_of_realifiedIdent_and_processionDatum
    {l : PrimeGeFive} (X : N8NativeInput l)
    {l' : PrimeGeFive} {V : Type} (I : OriginalInput l' V) (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l')
    (D : I.SourceUnitRegionHaarData v R n) (vp : GlobalPrimeIndex (X := X))
    (hid : S3135ValueMonoidRealifiedIdentification X I v R vp)
    (hd : S3135ProcessionScalingUnitDatum I v R n D) :
    FrontierHeightComparisonClause (I.sourceUnitRegionHaarInterface v R n D)
      (fun _ _ a b c => abcSourcePoint I v R a b c) :=
  s3135_actualF4_of_realizationLogDegree I v R n D
    (fun r => by
      have hc := s3135_compatibility_of_realifiedIdentification X I v R vp hid r
      rw [normalizedRealifiedPrimePowerHom_degree (X := X) vp] at hc
      exact congrArg Multiplicative.toAdd hc)
    (s3135_procession_scaling_unit_degree_zero I v R n D hd)

#check s3135_actualF4_of_realifiedIdent_and_processionDatum
end LeanFormal.IUT.XiFPaper.S3135F4BothByConstructionActual
end