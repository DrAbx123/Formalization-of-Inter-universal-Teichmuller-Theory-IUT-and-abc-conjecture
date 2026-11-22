import tmp.sheaf.xif.paper.S3136LGPBadToAllPlaceTransportsActual

/-! # Stage-4 host: log-shell place agreement for the bad family

Source anchors: IUT III, Prop. 3.2, (ii) (pp. 97--99); qpilot
S3133BadToAllPlaceIndexInjectionActual.

Conditional on the bad<->C3 index equivalence and the qpilot injection, the
selected actual log-shell places agree: c3LogShellPlace at e b equals
c3LogShellPlace at the injected all-place index.  This is the place-level form
of the tensorPlace agreement used by the packet fibers.

LABEL: prerequisite component only.  Consumer: lattice stream, stepxi C2. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPBadFamilyLogPlaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.S3133BadToAllPlaceIndexInjectionActual
open LeanFormal.IUT.XiFPaper.S3136LGPBadToAllPlaceTransportsActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The selected actual log-shell places agree under the qpilot injection. -/
theorem lgpBadFamilyLogPlace_eq
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (indexEquiv : V ≃ C3.tensorIndex)
    (h : S3133BadToAllPlaceIndexInjection T C3 e indexEquiv)
    (b : Bad (nativePlaceSelection T)) :
    c3LogShellPlace C3 (e b) =
      c3LogShellPlace C3 (indexEquiv (h.badToV b)) := by
  unfold c3LogShellPlace
  exact lgpBadFamilyIndex_agree T C3 e indexEquiv h b

#check lgpBadFamilyLogPlace_eq

end LeanFormal.IUT.XiFPaper.S3136LGPBadFamilyLogPlaceActual
end