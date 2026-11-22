/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5HproductFromFiniteIndexDataActual
import tmp.sheaf.xif.paper.Mzk1B5FiniteIndexDataFromBridgeActual
import tmp.sheaf.xif.paper.Mzk1B5FiniteIndexExpansionIffActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataNonDiagonalExactActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1B5HproductGeneralAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataActual
open LeanFormal.IUT.XiFPaper.Mzk1B5HproductFromFiniteIndexDataActual
open LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataFromBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexExpansionIffActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem finiteIndexData_iff_bridge_of_arch_zero
    (O : PaperDeterminantLogVolume.LineBundle (k := T.arithmetic.K))
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH dO : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (f : T.arithmetic.Kˣ)
    (harch : archimedeanContribution T f = 0) :
    FiniteIndexData T O s dH dO ↔
      B5ProductFormulaBridge T O s dH dO f := by
  constructor
  · intro D
    exact b5ProductFormulaBridge_of_finiteIndexData T O s dH dO f D harch
  · intro h
    exact finiteIndexData_of_productFormulaBridge T O s dH dO f h harch


end LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataNonDiagonalExactActual
