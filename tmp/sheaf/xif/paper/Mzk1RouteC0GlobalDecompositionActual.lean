import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeV2Actual
import tmp.sheaf.xif.paper.Mzk1NormArchCKActual
import tmp.sheaf.xif.paper.Mzk1NormArchConsumerActual
import Mathlib.Tactic

/-!
# Route C0: explicit finite + arch conditional decomposition

The finite bad-prime part is the actual C0 q-lattice Haar log.  The arch part
is the actual IUT IV hArc with explicit archCK.  The global log equality is
NOT constructed: C0 has no global readout type or C0->global arrow.  This file
defines the decomposition interface only; it is not a comparison and not an
unconditional global formula.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1RouteC0GlobalDecompositionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchConsumerActual
open LeanFormal.IUT.IUTIV.Estimates
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Finite bad-prime part: log Haar of the corrected C0 product q-lattice. -/
noncomputable def c0FiniteLog : Real :=
  Real.log (rootExtensionProductHaar T (c0ProductQ T)).toReal

variable {K : Type} [Field K] [NumberField K]

/-- Arch part: the actual IUT IV hArc with explicit archCK. -/
noncomputable def c0ArchPart (x : K) : Real := hArc K x

theorem c0ArchPart_eq_archCK (x : K) :
    c0ArchPart (K := K) x = archCK K *
      ∑ w : NumberField.InfinitePlace K, hTerm K (.infinite w) x :=
  hArc_eq_archCK_mul_sum x

theorem c0ArchPart_nonneg (x : K) : 0 ≤ c0ArchPart (K := K) x := by
  unfold c0ArchPart
  exact hArc_nonneg_via_archCK (F := K) x

/-- Conditional decomposition interface: the global readout is supplied, not
constructed.  The equality to finite+arch is the exact missing source arrow. -/
structure C0GlobalDecomposition
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (K : Type) [Field K] [NumberField K] (x : K) where
  globalReadout : Real
  globalReadout_eq : globalReadout = c0FiniteLog T + c0ArchPart (K := K) x

theorem C0GlobalDecomposition.decomposition
    (D : C0GlobalDecomposition T K x) :
    D.globalReadout = c0FiniteLog T + c0ArchPart (K := K) x :=
  D.globalReadout_eq

#print axioms C0GlobalDecomposition.decomposition

end LeanFormal.IUT.XiFPaper.Mzk1RouteC0GlobalDecompositionActual
