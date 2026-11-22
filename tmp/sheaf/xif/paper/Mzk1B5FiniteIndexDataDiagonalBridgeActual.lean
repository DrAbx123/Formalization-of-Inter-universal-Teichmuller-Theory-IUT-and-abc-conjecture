/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5FiniteIndexDataFromBridgeActual
import tmp.sheaf.xif.paper.Mzk1B5HproductDiagonalActual
import tmp.sheaf.xif.paper.Mzk1B5FiniteIndexDataDiagonalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataDiagonalBridgeActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataActual
open LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataFromBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1B5HproductDiagonalActual
open LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataDiagonalActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem finiteIndexDataDiagonal_of_bridge
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (hH : (badPrimeSource T).qPilotLineBundle ≠ 0) :
    FiniteIndexData T (badPrimeSource T).qPilotLineBundle s dH dH :=
  finiteIndexData_of_productFormulaBridge T (badPrimeSource T).qPilotLineBundle s dH dH
    (1 : T.arithmetic.Kˣ)
    (b5ProductFormulaBridge_diagonal T s dH hH)
    (archimedeanContribution_one_eq_zero T)


end LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataDiagonalBridgeActual
