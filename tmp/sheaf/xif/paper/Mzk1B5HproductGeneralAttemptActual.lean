/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual
import tmp.sheaf.xif.paper.Mzk1B5RelativeDetLogExpansionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1B5HproductGeneralAttemptActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1B5RelativeDetLogExpansionActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
def FiniteIndexExpansion
    (O : PaperDeterminantLogVolume.LineBundle (k := T.arithmetic.K))
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH dO : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v) : Prop :=
  finiteIndexContribution T (badPrimeSource T).qPilotLineBundle O s dH dO =
    relativeDetLog (k := T.arithmetic.K) (badPrimeSource T).qPilotLineBundle O
theorem b5ProductFormulaBridge_of_finiteIndexExpansion
    (O : PaperDeterminantLogVolume.LineBundle (k := T.arithmetic.K))
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH dO : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (f : T.arithmetic.Kˣ)
    (hfin : FiniteIndexExpansion T O s dH dO)
    (harch : archimedeanContribution T f = 0) :
    B5ProductFormulaBridge T O s dH dO f := by
  unfold B5ProductFormulaBridge
  unfold FiniteIndexExpansion at hfin
  rw [harch, hfin]
end LeanFormal.IUT.XiFPaper.Mzk1B5HproductGeneralAttemptActual
