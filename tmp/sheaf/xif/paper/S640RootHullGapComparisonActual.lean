import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.BadPlaceRootHullScalingFormulaActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

/-! # S640: existing root-hull gap and qPilot comparison

This file does not introduce a new theta carrier or procession.  It uses the
existing actual root theta hull (`rootThetaHull`/`rootThetaHullLog`) and the
existing qPilot comparison `qPilotClassicalLog_le_rootThetaHullLog`, at the
existing half coefficient c_norm/(2l).  The paper-coefficient formula equality
`PaperRootHullFormulaGap` remains the exact missing hull equality.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S640RootHullGapComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.BadPlaceRootHullScalingFormulaActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The existing actual qPilot classical region is contained in the half-root
theta hull.  This is the existing qPilot comparison at c_norm/(2l), not the
paper coefficient order/(2l). -/
theorem qPilotClassicalLog_le_halfRootThetaHullLog
    (hpos : 0 < Measure.addHaar
      (qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple
        (qVFamNormalizedCoefficientFamily T b)))
    (hfin : Measure.addHaar
      (rootThetaHull (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (halfCoefficientFamily T b)) < ⊤) :
    qPilotClassicalLog (qVFamTensorPlaces T b) qVFamTensorTuple
        Measure.addHaar (qVFamNormalizedCoefficientFamily T b)
        (qVFamNormalizedPureFractionalScalingData T b) ≤
      rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        Measure.addHaar (halfCoefficientFamily T b) := by
  refine qPilotClassicalLog_le_rootThetaHullLog
    (l := l) (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (μ := Measure.addHaar) (cNorm := qVFamNormalizedCoefficientFamily T b)
    (cRoot := halfCoefficientFamily T b)
    (dataNorm := qVFamNormalizedPureFractionalScalingData T b) ?_ ?_ ?_ ?_ ?_
  · intro i
    unfold halfCoefficientFamily
    have hc : 0 ≤ qVFamNormalizedCoefficient T b := qVFamNormalizedCoefficient_nonneg T b
    have hl : (2 : Real) ≤ (2 * l.value : Real) := by
      have hfive : 5 ≤ l.value := l.ge_five
      exact_mod_cast (by omega : 2 ≤ 2 * l.value)
    exact div_le_self hc (by linarith)
  · exact oneLabel l
  · exact gaussExponent_oneLabel l
  · exact hpos
  · exact hfin

/-- The paper-coefficient formula equality is exactly the existing
`PaperRootHullFormulaGap`: the paper root hull must equal the single
fractional-lattice scaled region at order(q_v)/(2l). -/
def PaperRootHullFormulaGapRequired : Prop :=
  Nonempty (PaperRootHullFormulaGap T b)

/-- Exact gap statement: without the existing hull equality, only the qPilot
containment comparison above is available; the logarithmic formula equality
is not asserted. -/
def PaperRootHullFormulaLogGap : Prop :=
  paperRootThetaHullLog T b Measure.addHaar =
    paperRootThetaFormulaLog T b

theorem paperRootHullFormulaLogGap_of_gap
    (G : PaperRootHullFormulaGap T b) :
    PaperRootHullFormulaLogGap T b :=
  paperRootThetaHullLog_eq_formula_of_gap T b Measure.addHaar G

end LeanFormal.IUT.XiFPaper.S640RootHullGapComparisonActual
end
