import tmp.sheaf.xif.paper.S1029S995FinalAuditActual
import tmp.sheaf.xif.paper.S1009HQHC3Actual
import tmp.sheaf.xif.paper.S991S983LinkInputsActual
import tmp.sheaf.xif.paper.S999HQHC3Actual
import tmp.sheaf.xif.paper.ThetaLinkFromSource

/-! # S1032: canonical Oa link instantiation

S1009 gives the canonical actual Oa with hC3 actual.  S991 constructs the
actual PaperXiFSourceLink from hQ and hC3.  Therefore hC3 is eliminated from
the link construction: the link depends only on the source-q identification hQ.

The remaining exact link input is the actual Theta-link identification
thetaSourceComparison (the paper source comparison), and finite link evidence.
No hC3 and no fake hlink. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1032CanonicalLinkInstantiationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1029S995FinalAuditActual
open LeanFormal.IUT.XiFPaper.S1009HQHC3Actual
open LeanFormal.IUT.XiFPaper.S991S983LinkInputsActual
open LeanFormal.IUT.XiFPaper.S999HQHC3Actual
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource
open LeanFormal.IUT.XiFPaper.S622PaperXiFFieldAuditActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S995FiniteCarrierCor312ConclusionActual
open LeanFormal.IUT.XiFPaper.S968FinalTensorInequalityCor312Actual
open MeasureTheory

universe uX uLabel uC3 uD3

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)

/-- Actual canonical PaperXiFSourceLink; hC3 is actual, only hQ is supplied. -/
noncomputable def s1032PaperXiFSourceLink
    (hQ : S999QPilotLogVolumeIdentification (l := l) I C3) :
    PaperXiFSourceLink (concreteO (l := l) I) P C3 :=
  s991PaperXiFSourceLink (l := l) I P C3
    (s1009CanonicalOa (l := l) I C1 C2 C3)
    (s1009Canonical_hC3 (l := l) I C1 C2 C3) hQ

/-- The canonical link's identification is the actual Theta source comparison. -/
theorem s1032LinkIdentification_eq
    (hQ : S999QPilotLogVolumeIdentification (l := l) I C3) :
    (s1032PaperXiFSourceLink (l := l) I P C1 C2 C3 hQ).link_identification =
      thetaSourceComparison (s1009CanonicalOa (l := l) I C1 C2 C3) P :=
  rfl

/-- Exact required source-q input: hC3 is no longer a separate input. -/
def S1032FinalRequired : Prop :=
  S999QPilotLogVolumeIdentification (l := l) I C3

/-- Exact remaining link input after hC3 elimination. -/
def S1032LinkIdentificationRequired
    (hQ : S999QPilotLogVolumeIdentification (l := l) I C3) : Prop :=
  (s1032PaperXiFSourceLink (l := l) I P C1 C2 C3 hQ).link_identification

end LeanFormal.IUT.XiFPaper.S1032CanonicalLinkInstantiationActual

end
