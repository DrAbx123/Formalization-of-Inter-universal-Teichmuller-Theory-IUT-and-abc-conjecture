import tmp.sheaf.xif.paper.S1015FractionalLatticeOpenActual
import tmp.sheaf.xif.paper.S1022LocalFracSpanTopActual
/-! # S1023: actual S923FractionalLatticeOpen from local span-top
Uses S1022 actual local span-top, then S1015 tensor-span openness. -/
noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1023FractionalLatticeOpenActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S1015FractionalLatticeOpenActual
open LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual
open LeanFormal.IUT.XiFPaper.S1022LocalFracSpanTopActual
open LeanFormal.IUT.LocalFieldLogarithm
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
theorem s923FractionalLatticeOpen_actual :
    S923FractionalLatticeOpen T b :=
  s923FractionalLatticeOpen_of_spanTop T b
    (fun i => S1022LocalFracSpanTopActual.span_padicFractionalLattice_eq_top
      (p := qVFamTensorP T b)
      (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
      (paperRootCoefficientFamily (l := l) T b i))
end LeanFormal.IUT.XiFPaper.S1023FractionalLatticeOpenActual
