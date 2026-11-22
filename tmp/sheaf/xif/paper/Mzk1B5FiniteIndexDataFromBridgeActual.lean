/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5FiniteIndexDataActual
import tmp.sheaf.xif.paper.Mzk1B5HproductGeneralAttemptActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataFromBridgeActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataActual
open LeanFormal.IUT.XiFPaper.Mzk1B5HproductGeneralAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem finiteIndexData_of_productFormulaBridge
    (O : PaperDeterminantLogVolume.LineBundle (k := T.arithmetic.K))
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH dO : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (f : T.arithmetic.Kˣ)
    (hbridge : B5ProductFormulaBridge T O s dH dO f)
    (harch : archimedeanContribution T f = 0) :
    FiniteIndexData T O s dH dO where
  eq := by
    unfold B5ProductFormulaBridge at hbridge
    rw [harch, add_zero] at hbridge
    exact hbridge.symm


end LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexDataFromBridgeActual
