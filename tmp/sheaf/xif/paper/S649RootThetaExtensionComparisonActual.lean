import tmp.sheaf.xif.paper.RootThetaExtensionHullCarrierActual
import tmp.sheaf.xif.paper.PaperC3RootThetaHullActual

/-! # S649: extension root Theta hull and conditional q-pilot comparison

Uses the actual extension-valued root Theta hull and paperRootThetaUnit.
The extension-to-completion hull map and root-hull log comparison are kept as
explicit conditional data; no completion 2l-root is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S649RootThetaExtensionComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperC3RootThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootThetaHullCarrierGapActual
open LeanFormal.IUT.XiFPaper.RootThetaExtensionHullCarrierActual

universe u v
variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Actual extension-valued root Theta carrier data. -/
noncomputable def s649CarrierData :
    RootThetaExtensionHullCarrierData (G := G) :=
  rootThetaExtensionHullCarrierData (G := G)

/-- Actual extension root Theta unit powers: the 2l-th power is the embedded
completion qUnit power, so no completion 2l-root is used. -/
theorem s649RootThetaPowerPoint_eq_embedded
    (j : ThetaLabel (l := l)) (v : V) :
    rootThetaPowerPoint (G := G) j v =
      (unitToAlgClosed (G.qUnit v) : RootExtension (G := G) v) ^
        (gaussExponent (thetaLabelToSigned (l := l) j).1).toNat :=
  rootThetaPowerPoint_eq_embedded_qUnit_power (G := G) j v

/-- Exact missing comparison package: an extension root-hull log comparison to
the q-pilot scalar, plus the extension-to-completion hull map. Both are explicit
propositions, not asserted. -/
structure S649RootThetaQPilotComparisonData where
  rootHullLogComparison : RootThetaHullLogComparison
  extensionToCompletionHullMap : RootThetaToCompletionHullMapGap

/-- Conditional package from explicit actual comparison data. -/
noncomputable def s649RootThetaQPilotComparisonDataOf
    (hcomparison : RootThetaHullLogComparison)
    (hmap : RootThetaToCompletionHullMapGap) :
    S649RootThetaQPilotComparisonData where
  rootHullLogComparison := hcomparison
  extensionToCompletionHullMap := hmap

/-- Exact minimal gap: the extension root-hull log comparison and the
extension-to-completion hull map. -/
def S649RootThetaQPilotComparisonRequired : Prop :=
  Nonempty (S649RootThetaQPilotComparisonData)

end LeanFormal.IUT.XiFPaper.S649RootThetaExtensionComparisonActual

end
