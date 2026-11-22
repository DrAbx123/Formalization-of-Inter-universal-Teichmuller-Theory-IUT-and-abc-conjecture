import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import tmp.sheaf.xif.paper.S2597CarrierBridgeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2600LogShellRealizationActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {v : V}

/-- A log-shell compatible refinement of `SourceImageRealization`: the
realization of positive reals is log-degree faithful at the place `v`.  This
is the exact extra field consumed by `sourceLocalLogDegree_constant` and
`sourceLocalLogDegree_thetaPilotPoint`. -/
structure SourceImageRealizationLogShell (v : V)
    extends I.SourceImageRealization v where
  hdeg : forall b : Real,
    I.logDegreeAt 0 0 v (posRealAction (Multiplicative.ofAdd b)) = b

theorem S2600_sourceLocalLogDegree_thetaPilotPoint
    (R : SourceImageRealizationLogShell I v)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R.toSourceImageRealization n j) =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j) :=
  I.sourceLocalLogDegree_thetaPilotPoint v R.toSourceImageRealization n j R.hdeg

#check SourceImageRealizationLogShell
#check S2600_sourceLocalLogDegree_thetaPilotPoint
#print axioms S2600_sourceLocalLogDegree_thetaPilotPoint

end LeanFormal.IUT.XiFPaper.S2600LogShellRealizationActual
end