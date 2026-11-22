import LeanFormal.IUT.Audit.Status

/-! # S3137: F4(b1) Haar-decomposition reuse record

F4(b1) (Haar uniqueness scalar step + log-shell scaling index) consumes the tree
Haar dilation-contraction log-volume decomposition and the unit-region Haar
interface instead of new definitions.
-/

namespace LeanFormal.IUT.XiFPaper.S3137F4b1HaarReuseActual

/-- F4(b1) reuse points. -/
def S3137F4b1HaarReuse : List (String × String × String) :=
  [ ("Haar dilation-contraction decomposition", "CardHullRealHaarDilationDocking.lean:178 dilationContractionLogVolumeScaleDecomposition_logVolume_singleton_eq_logShell", "REUSE/ADAPT: scalar-factor/log-shell index side of F4(b1)"),
    ("unit-region Haar interface", "IQCarrierHaarData.lean:181 sourceUnitRegionHaarInterface", "REUSE"),
    ("unit scaling interface", "IQCarrierHaarData.lean:265 sourceHullUnitScalingInterface", "REUSE"),
    ("Haar uniqueness tool", "S3135HaarUniquenessToolActual.s3135_haarUniquenessScalarStep_proved (abc)", "REUSE: scalar step already proved"),
    ("trivial-scaling finding", "all 3 SourceUnitRegionHaarData constructors have scaling := 1 (SourceUnitRegionHaarDataActual:421, SourceContractedSupplyRealization:226, OModuleCompactnessLayer:197)", "FLAG: nontrivial-lambda instance absent; F4(b) nontrivial scaling remains paper input (A12/A13)") ]

theorem S3137F4b1HaarReuse_length : S3137F4b1HaarReuse.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.S3137F4b1HaarReuseActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: F4(b1) reuse. -/
def S3137F4b1HaarReuseRecord : Obligation :=
  { id := "INDEX.F4.b1.haar-decomposition-reuse"
    source := "CardHullRealHaarDilationDocking:178; IQCarrierHaarData:181/265; S3135HaarUniquenessToolActual"
    status := VerificationStatus.interface
    note := "F4(b1) REUSE: Haar dilation-contraction log-volume decomposition (CardHullRealHaarDilationDocking:178), unit-region Haar interface and unit scaling interface (IQCarrierHaarData:181/265), and the proved Haar uniqueness scalar step (S3135HaarUniquenessToolActual) supply the F4(b1) scalar-factor/log-shell index side. FLAG unchanged: all three SourceUnitRegionHaarData constructors are scaling := 1; no nontrivial-lambda instance; nontrivial F4(b) remains paper input (A12/A13)."
    dependsOn := ["S3137F4b1HaarReuseActual", "INDEX.PRIOR-ART.f4-clause-hull"] }

end LeanFormal.IUT.Audit
