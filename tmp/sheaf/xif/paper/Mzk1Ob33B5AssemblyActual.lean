/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.xif.paper.Mzk1Ob33B5IndexActual
import tmp.sheaf.xif.paper.Mzk1Ob33ArchMetricActual
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineBridgeActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual

/-!
# Route B #3 step 5: conditional B5 assembly to relativeDetLog

Combines the finite-place rank-one index, the archimedean compatibility, and the
mainline Ob33DefLineBridge relativeDeterminant identity.  The local-global product
formula is an EXPLICIT hypothesis (GAP), not a structure field or a completed input.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.PaperOModuleActual
open scoped BigOperators
open LeanFormal.IUT.XiFPaper.Mzk1Ob33ArchMetricActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Finite-place B5 index contribution: negative relative index times log p,
summed over a selected finite set of places. -/
noncomputable def finiteIndexContribution
    (H O : PaperDeterminantLogVolume.LineBundle (k := T.arithmetic.K))
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH dO : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v) : Real :=
  ∑ v ∈ s,
    - (((PaperOModuleActual.localValuation (k := T.arithmetic.K) v (dH v) -
        PaperOModuleActual.localValuation (k := T.arithmetic.K) v (dO v) : Int) : Real) *
        Real.log (residueCharacteristic v : Real))

/-- Archimedean weight from the actual metric normalization. -/
noncomputable def archimedeanContribution (f : T.arithmetic.Kˣ) : Real :=
  Mzk1Ob33ArchMetricActual.archDetMetricWeight (F := T.arithmetic.K) f

/-- **Conditional B5 assembly**: if the local-global product formula holds, the
actual q-pilot arithmetic degree is the finite index sum plus the archimedean
contribution plus the reference log-volume. -/
theorem qPilotDetArithmeticDegree_eq_finiteIndex_add_arch_add_global
    (O : PaperDeterminantLogVolume.LineBundle (k := T.arithmetic.K))
    (hH : (badPrimeSource T).qPilotLineBundle ≠ 0) (hO : O ≠ 0)
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH dO : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (f : T.arithmetic.Kˣ)
    (hproduct : relativeDetLog (k := T.arithmetic.K)
        (badPrimeSource T).qPilotLineBundle O =
      finiteIndexContribution T (badPrimeSource T).qPilotLineBundle O s dH dO +
        archimedeanContribution T f) :
    qPilotDetArithmeticDegreeOfBadPrimes T =
      finiteIndexContribution T (badPrimeSource T).qPilotLineBundle O s dH dO +
        archimedeanContribution T f +
        PaperDeterminantLogVolume.globalLogVolume (k := T.arithmetic.K) O := by
  rw [qPilotDetArithmeticDegreeOfBadPrimes_eq_relativeDetLog_add T O hH hO, hproduct]

/-- The Route B gap in finite-index + arch form, under the same product-formula
GAP hypothesis. -/
theorem routeB_gap_iff_finiteIndex_arch
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (O : PaperDeterminantLogVolume.LineBundle (k := T.arithmetic.K))
    (hH : (badPrimeSource T).qPilotLineBundle ≠ 0) (hO : O ≠ 0)
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH dO : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (f : T.arithmetic.Kˣ)
    (hproduct : relativeDetLog (k := T.arithmetic.K)
        (badPrimeSource T).qPilotLineBundle O =
      finiteIndexContribution T (badPrimeSource T).qPilotLineBundle O s dH dO +
        archimedeanContribution T f) :
    RouteBArithmeticDegreeReadingGap T.arithmetic (badPrimeSource T) C3 ↔
      finiteIndexContribution T (badPrimeSource T).qPilotLineBundle O s dH dO +
        archimedeanContribution T f +
        PaperDeterminantLogVolume.globalLogVolume (k := T.arithmetic.K) O =
        routeBThetaNormalized C3 := by
  rw [routeB_gap_iff_relativeDetLog_form T C3 O hH hO, hproduct]

def b5AssemblyRows : List (String × String × String) :=
  [ ("finiteIndexContribution", "sum finite index contributions", "CONSTRUCTED (from LocalGeneratorData)"),
    ("archimedeanContribution", "actual archDetMetricWeight", "CONSTRUCTED"),
    ("qPilotDetArithmeticDegree_eq_finiteIndex_add_arch_add_global", "conditional B5 assembly", "PROVED conditional on product formula"),
    ("product formula / local-global bridge", "global log = finite index sum + arch", "EXACT GAP (explicit hproduct)") ]

theorem b5AssemblyRows_length : b5AssemblyRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual

-- retry marker after import/open fixes
