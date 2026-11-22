import LeanFormal.IUT.Audit.Status

/-! # S3156: REPO-FIRST prior-art audit - model Haar / scaling / OriginalInput

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Prior-art rows for model Haar/scaling/OriginalInput work. -/
def S3156ModelHaarPriorArt : List (String × String × String) := [
  ("LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/IQCarrierHaarData.lean", "structure SourceUnitRegionHaarData + sourceUnitRegionHaarInterface etc.", "REUSE the carrier/Haar-data interface; do not redefine"),
  (".../IQCarrierConcreteModel.lean", "concrete IQ carrier model (34k)", "REUSE model constructions before writing new definitions"),
  (".../SourceUnitRegionHaarDataActual.lean", "concrete nonpositive value model + prime-strip/theater family + sourceHaarActualOriginalInput", "REUSE for model value/theater/OriginalInput"),
  (".../SourceArithmeticThetaPilotBridge.lean / PadicLogShellModel.lean", "theta-pilot bridge / padic log-shell model", "REUSE for theta packet/log-shell model data"),
  (".../SourceHullInterfaceDischarge.lean / SourceImageHull.lean", "hull interface discharge / image hull", "REUSE hull-side facts"),
  (".../HullDeterminantLogVolumeReduction.lean", "determinant log-volume reduction", "REUSE for hull log-volume reductions") ]

theorem S3156ModelHaarPriorArt_length : S3156ModelHaarPriorArt.length = 6 := rfl

/-- Prior-art audit record: model Haar/scaling/OriginalInput. -/
def S3156PriorArtModelHaar : Obligation :=
  { id := "IUT.project.prior-art-model-haar"
    source := "Lead §7.9 directive; Corollary312/StepXI/HolomorphicHull tree survey"
    status := VerificationStatus.interface
    note :=
      "PRIOR ART CONFIRMED (model Haar/scaling/OriginalInput): IQCarrierHaarData defines the "
      ++ "SourceUnitRegionHaarData interface; IQCarrierConcreteModel and SourceUnitRegionHaarData"
      ++ "Actual already build concrete models (value monoid, realization, prime strips, theater "
      ++ "family, OriginalInput); SourceArithmeticThetaPilotBridge/PadicLogShellModel provide "
      ++ "theta-packet/log-shell model data; SourceHullInterfaceDischarge/SourceImageHull/"
      ++ "HullDeterminantLogVolumeReduction provide hull facts. RULE: search these first; adapt, "
      ++ "do not re-prove."
    dependsOn := [] }

#check S3156PriorArtModelHaar
#check S3156ModelHaarPriorArt_length

end LeanFormal.IUT.Audit
