import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CertificateCThetaTransfer
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Actual signed hull log-volume is nonpositive, hence satisfies the trivial
upper estimate with constant `0`: `-|log Theta| <= 0 * |log q|`. -/
theorem S2714_sourceSignedHull_upper_zero
    (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (q : Real) :
    I.sourceSignedHullLogVolume v R n <= (0 : Real) * |Real.log q| := by
  rw [zero_mul]
  exact I.sourceSignedHullLogVolume_nonpos v R n

/-- The actual Step (xi-f) arithmetic transfer: any upper estimate
`theta <= C * |log q|` plus the inclusion `-|log q| <= theta` yields
`-1 <= C`.  This is the existing actual `cor312CThetaLowerBound`. -/
theorem S2714_cThetaLowerBound_of_upper
    {theta q : Real} (hq : Real.log q ≠ 0)
    (hincl : -|Real.log q| ≤ theta) {C : Real}
    (hupper : theta ≤ C * |Real.log q|) :
    -1 ≤ C :=
  cor312CThetaLowerBound hq hincl hupper

#print axioms S2714_sourceSignedHull_upper_zero
#print axioms S2714_cThetaLowerBound_of_upper

end LeanFormal.IUT.XiFPaper.S2714CThetaUpperInventoryActual
end
