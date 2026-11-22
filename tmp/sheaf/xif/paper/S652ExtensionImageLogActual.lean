import tmp.sheaf.xif.paper.PaperRootThetaProductMeasureActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S652ExtensionImageLogActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperRootThetaProductMeasureActual
open LeanFormal.IUT.XiFPaper.PaperRootThetaProductCarrierActual
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open scoped BigOperators

universe u v
variable {l : PrimeGeFive} {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
variable [MeasurableSpace (RootThetaProductCarrier (G := G))]

/-- Actual finite-image log: logarithm of the Dirac image measure of the
product unit ball. -/
noncomputable def extensionImageLog
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) : Real :=
  Real.log ((rootThetaImageMeasure (G := G)
    (rootThetaUnitBall (G := G))).toReal)

/-- The image log is the logarithm of the signed-label cardinality. -/
theorem extensionImageLog_eq_log_card
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    extensionImageLog (G := G) hq =
      Real.log (Fintype.card (ThetaLabel (l := l)) : Real) := by
  unfold extensionImageLog
  rw [rootThetaImageMeasure_unitBall (G := G) hq]
  rw [ENNReal.toReal_natCast]

/-- The actual q-pilot scalar used for comparison: log of the theta packet q. -/
noncomputable def qPilotScalar : Real :=
  Real.log G.thetaPacket.q

/-- Exact comparison proposition: the finite-image log equals the q-pilot
scalar.  No inhabitant is provided. -/
def ExtensionImageLogQPilotComparison
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) : Prop :=
  extensionImageLog (G := G) hq = qPilotScalar (G := G)

/-- Exact missing product Haar/measure; the Dirac image measure is not Haar. -/
def ExtensionImageHaarGap : Prop :=
  RootThetaProductHaarGapRequired

end LeanFormal.IUT.XiFPaper.S652ExtensionImageLogActual

end
