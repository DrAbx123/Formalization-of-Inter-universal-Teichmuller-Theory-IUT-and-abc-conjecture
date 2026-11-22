/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ExactHullVUpperBoundActual
import tmp.sheaf.xif.paper.Mzk1ExactHullVLocalBoundActual
import Mathlib.Tactic

/-! # CONDITIONAL #7 assembly: per-place local bounds → hull V upper bound -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ExactHullVAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ExactHullVUpperBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1ExactHullVLocalBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open MeasureTheory
open scoped BigOperators

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

structure HullVUpperBoundLocalAssembly where
  log_d : Real
  log_f : Real
  C0 : Real
  localBoundData : ∀ b : Bad (nativePlaceSelection T), LocalBallLogBound (T := T) b
  sum_le : (∑ b : Bad (nativePlaceSelection T), (localBoundData b).bound) ≤
    (1 / 4 : Real) * (l.value : Real) * (log_d + log_f) + C0

def HullVUpperBoundLocalAssembly.toData
    (A : HullVUpperBoundLocalAssembly (T := T)) :
    HullVUpperBoundData (T := T) where
  log_d := A.log_d
  log_f := A.log_f
  C0 := A.C0
  localBound := fun b => (A.localBoundData b).bound
  local_le := fun b => (A.localBoundData b).le
  sum_le := A.sum_le

theorem normalizedLog_hull_le_of_local
    (A : HullVUpperBoundLocalAssembly (T := T)) :
    rootExtensionProductNormalizedLog T (s1902Hull T) ≤
      (1 / 4 : Real) * (l.value : Real) * (A.log_d + A.log_f) + A.C0 :=
  normalizedLog_hull_le_of_data (T := T) A.toData

def rows : List String := ["local per-place bounds", "global sum bound", "conditional V upper bound"]
theorem rows_length : rows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ExactHullVAssemblyActual

end