/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ExactHullVMainTermActual
import tmp.sheaf.xif.paper.Mzk1MainTermActualNonnegActual
import Mathlib.Tactic
/-! # #7 actual bound: normalizedLog hull <= (1/4)l(log disc + log cond) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1MainTermActualBoundActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ExactHullVMainTermActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1MainTermActualNonnegActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDCurveDataSourceActual
open MeasureTheory
universe u
variable {l : PrimeGeFive} {ι : Type u}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem normalizedLog_hull_le_actualMainTerm (M : CurveData ι) (E : ι) :
    rootExtensionProductNormalizedLog T (s1902Hull T) ≤
      (1 / 4 : Real) * (l.value : Real) *
        (Real.log (M.disc E : Real) + Real.log (M.cond E : Real)) :=
  normalizedLog_hull_le_mainTerm (T := T) (l := l)
    (Real.log (M.disc E : Real)) (Real.log (M.cond E : Real))
    (mainTerm_nonneg_actual (l := l) M E)
end LeanFormal.IUT.XiFPaper.Mzk1MainTermActualBoundActual
end