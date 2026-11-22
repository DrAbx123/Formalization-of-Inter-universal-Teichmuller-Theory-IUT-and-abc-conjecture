/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5FiniteIndexDataActual
import tmp.sheaf.xif.paper.Mzk1B5RelativeDetLogSelfActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataDiagonalActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1B5HproductGeneralAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataActual
open LeanFormal.IUT.XiFPaper.Mzk1B5RelativeDetLogSelfActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
noncomputable def finiteIndexDataDiagonal
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (hH : (badPrimeSource T).qPilotLineBundle ≠ 0) :
    FiniteIndexData T (badPrimeSource T).qPilotLineBundle s dH dH where
  eq := by
    have hrel := relativeDetLog_self (k := T.arithmetic.K)
      (badPrimeSource T).qPilotLineBundle hH
    have hfin : finiteIndexContribution T (badPrimeSource T).qPilotLineBundle
        (badPrimeSource T).qPilotLineBundle s dH dH = 0 := by
      unfold finiteIndexContribution
      simp
    rw [hrel, hfin]


end LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataDiagonalActual
