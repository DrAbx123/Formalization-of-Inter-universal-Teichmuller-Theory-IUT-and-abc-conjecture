import tmp.sheaf.xif.paper.PaperC3KummerExtensionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Basic

-- Actual normed local Kummer field L_v inside the spectral-normed
-- SourceAlgebraicClosure, its finite-dimensional completeness, and the
-- FinitePadicTensor/Haar/log-volume construction.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperKummerLocalTensorNormedActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open MeasureTheory
open scoped BigOperators

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

abbrev SourceClosure (v : V) : Type u :=
  SourceAlgebraicClosure (G.place v).val

noncomputable def sourceRootValue (v : V) : SourceClosure (G := G) v :=
  (twoLthRootAt (G := G) v : AlgebraicClosure (CommonPrimeCompletion (G.place v)))

abbrev L (v : V) : Type u :=
  IntermediateField.adjoin (CommonPrimeCompletion (G.place v))
    ({sourceRootValue (G := G) v} : Set (SourceClosure (G := G) v))

instance lField (v : V) : Field (L (G := G) v) := inferInstance

instance lNormedField (v : V) : NormedField (L (G := G) v) := inferInstance

instance lMeasurableSpace (v : V) : MeasurableSpace (L (G := G) v) := borel _

instance lNormedSpaceCompletion (v : V) :
    NormedSpace (CommonPrimeCompletion (G.place v)) (L (G := G) v) := inferInstance

instance lFiniteDimensionalCompletion (v : V) :
    FiniteDimensional (CommonPrimeCompletion (G.place v)) (L (G := G) v) := by
  apply IntermediateField.adjoin.finiteDimensional
  exact IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic (sourceRootValue (G := G) v))

instance lCompleteSpace (v : V) : CompleteSpace (L (G := G) v) :=
  FiniteDimensional.complete (CommonPrimeCompletion (G.place v)) (L (G := G) v)

noncomputable def lHaar (v : V) : Measure (L (G := G) v) := Measure.addHaar

#check SourceClosure
#check sourceRootValue
#check L
#check lField
#check lNormedField
#check lMeasurableSpace
#check lCompleteSpace
#check lHaar

end LeanFormal.IUT.XiFPaper.PaperKummerLocalTensorNormedActual

end