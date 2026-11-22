/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5ArchActual
import tmp.sheaf.xif.paper.Mzk1DetLineConstructionActual
import Mathlib.Tactic

/-! # Route B #3: merged PlaceB5 finite + arch declaration -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5MergedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5ArchActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual

variable {l : PrimeGeFive}
variable {k : Type} [Field k] [NumberField k]

/-- The finite B5 part in the form consumed by the merged log-degree. -/
noncomputable def finiteB5Part {H O : LineBundle (k := k)}
    {v : NumberField.FinitePlace k} (dH : LocalGeneratorData (k := k) H v)
    (dO : LocalGeneratorData (k := k) O v) (vH vO : Int) (logp : Real) : Real :=
  -( ((vH - vO : Int) : Real) ) * logp

/-- The finite B5 part equals the difference of the place log-volumes when the
per-place B5 target holds. -/
theorem finiteB5Part_eq_placeLogVolume_sub {H O : LineBundle (k := k)}
    {v : NumberField.FinitePlace k} (dH : LocalGeneratorData (k := k) H v)
    (dO : LocalGeneratorData (k := k) O v) (vH vO : Int) (logp : Real)
    (hB5 : PlaceB5Target (k := k) dH dO vH vO logp) :
    finiteB5Part (k := k) dH dO vH vO logp =
      placeLogVolume dH - placeLogVolume dO :=
  hB5.symm

/-- The merged log-degree with the finite part written via B5 valuations. -/
theorem mergedLogDegree_B5 (T : SourceNativeInitialThetaData.{0} l)
    {H O : LineBundle (k := T.arithmetic.K)}
    {v : NumberField.FinitePlace T.arithmetic.K}
    (dH : LocalGeneratorData (k := T.arithmetic.K) H v)
    (dO : LocalGeneratorData (k := T.arithmetic.K) O v)
    (vH vO : Int) (logp archSum : Real)
    (hB5 : PlaceB5Target (k := T.arithmetic.K) dH dO vH vO logp) :
    mergedLogDegree T (finiteB5Part (k := T.arithmetic.K) dH dO vH vO logp) archSum =
      mergedLogDegree T (placeLogVolume dH - placeLogVolume dO) archSum := by
  rw [finiteB5Part_eq_placeLogVolume_sub dH dO vH vO logp hB5]

/-- Nonnegativity of the merged log-degree once the B5 valuation difference and the
archimedean sum are nonnegative. -/
theorem mergedLogDegree_B5_nonneg (T : SourceNativeInitialThetaData.{0} l)
    {H O : LineBundle (k := T.arithmetic.K)}
    {v : NumberField.FinitePlace T.arithmetic.K}
    (dH : LocalGeneratorData (k := T.arithmetic.K) H v)
    (dO : LocalGeneratorData (k := T.arithmetic.K) O v)
    (vH vO : Int) (logp archSum : Real)
    (hB5 : PlaceB5Target (k := T.arithmetic.K) dH dO vH vO logp)
    (hfinite : 0 <= finiteB5Part (k := T.arithmetic.K) dH dO vH vO logp)
    (harch : 0 <= archSum) :
    0 <= mergedLogDegree T (placeLogVolume dH - placeLogVolume dO) archSum :=
  mergedLogDegree_nonneg T
    (by rw [← finiteB5Part_eq_placeLogVolume_sub dH dO vH vO logp hB5]; exact hfinite)
    harch

def placeB5MergedRows : List (String × String × String) :=
  [ ("finiteB5Part", "-(vH-vO)logp as the finite B5 part", "DEF"),
    ("finiteB5Part_eq_placeLogVolume_sub", "B5 target => finite part = placeLogVolume difference", "PROVED"),
    ("mergedLogDegree_B5", "merged log-degree with B5 valuations", "PROVED"),
    ("mergedLogDegree_B5_nonneg", "merged nonneg from finite/arch nonneg", "PROVED") ]

theorem placeB5MergedRows_length : placeB5MergedRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5MergedActual

end