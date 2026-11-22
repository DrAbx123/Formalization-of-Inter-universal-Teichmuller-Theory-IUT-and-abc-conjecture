/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.OModuleActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineFromBadPrimeSourceActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual

/-! # B5 assembly without hproduct: named bridge attempt / exact GAP -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperDeterminantLogVolume
open PaperOModuleActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Named local-global bridge: the relative determinant log equals the finite
index sum plus the archimedean contribution. -/
def B5ProductFormulaBridge
    (O : PaperDeterminantLogVolume.LineBundle (k := T.arithmetic.K))
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH dO : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (f : T.arithmetic.Kˣ) : Prop :=
  relativeDetLog (k := T.arithmetic.K) (badPrimeSource T).qPilotLineBundle O =
    finiteIndexContribution T (badPrimeSource T).qPilotLineBundle O s dH dO +
      archimedeanContribution T f

/-- Conditional assembly using the named bridge (no anonymous hproduct). -/
theorem qPilotDetArithmeticDegree_eq_finiteIndex_add_arch_add_global_of_bridge
    (O : PaperDeterminantLogVolume.LineBundle (k := T.arithmetic.K))
    (hH : (badPrimeSource T).qPilotLineBundle ≠ 0) (hO : O ≠ 0)
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH dO : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (f : T.arithmetic.Kˣ)
    (hbridge : B5ProductFormulaBridge T O s dH dO f) :
    qPilotDetArithmeticDegreeOfBadPrimes T =
      finiteIndexContribution T (badPrimeSource T).qPilotLineBundle O s dH dO +
        archimedeanContribution T f +
        PaperDeterminantLogVolume.globalLogVolume (k := T.arithmetic.K) O :=
  by
    simpa [B5ProductFormulaBridge] using
      qPilotDetArithmeticDegree_eq_finiteIndex_add_arch_add_global T O hH hO s dH dO f hbridge

/-- Exact GAP: the named bridge is not proved. -/
def MissingB5ProductFormulaBridge : Prop :=
  ∀ (O : PaperDeterminantLogVolume.LineBundle (k := T.arithmetic.K))
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH dO : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (f : T.arithmetic.Kˣ), B5ProductFormulaBridge T O s dH dO f

def assemblyNoHproductRows : List (String × String × String) :=
  [ ("B5ProductFormulaBridge", "relativeDetLog = finite index + arch", "NAMED BRIDGE (GAP)"),
    ("qPilotDetArithmeticDegree_eq_finiteIndex_add_arch_add_global_of_bridge", "assembly via named bridge", "PROVED conditional"),
    ("MissingB5ProductFormulaBridge", "full local-global product formula", "EXACT GAP (not asserted)") ]

theorem assemblyNoHproductRows_length : assemblyNoHproductRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
