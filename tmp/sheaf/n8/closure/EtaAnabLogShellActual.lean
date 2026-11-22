import tmp.sheaf.n8.closure.C2Native
import tmp.sheaf.n8.closure.EtaRssLogShellLine
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer
import Mathlib

/-!
# etaAnab actual log-shell data

Builds the actual log-shell integral structure from the production local shell
and the production log-shell/volume container interface.  `Rss` is the qside actual
log-shell line (`EtaRssLogShellLineData`), not the bare real line; the Kummer vertical layer and Ind1/2/3 are registered exactly, with the
missing actual vertical correspondence as the named source gap.  No direct
Q/hull comparison is introduced.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.EtaRssLogShellLine

namespace LeanFormal.IUT.N8Closure.EtaAnabLogShellActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual local log-shell datum from the native bad finite place. -/
noncomputable def localShell : SourceLogShellDatum :=
  C2Native.nativeLocalShell X

/-- Actual log-shell integral structure. -/
def integralStructure : Set (localShell X).K :=
  (localShell X).logShell

theorem integralStructure_eq :
    integralStructure X = (localShell X).logShell := rfl

/-- Actual unit layer of the log-shell. -/
def unitLayer : Set (localShell X).K :=
  (localShell X).unitLayer

/-- The actual Rss carrier: qside log-shell line data, not the bare real line. -/
abbrev Rss : Type := EtaRssLogShellLineData X

/-- The actual log-shell Rss point for the native log-shell data. -/
noncomputable def etaAnabRss : Rss X :=
  etaRssLogShellLineData X

/-- The Rss shell agrees with the etaAnab local shell. -/
theorem etaAnabRss_shell_eq :
    (etaAnabRss X).shell = (localShell X).logShell := rfl

/-- Exact handling of Ind1/Ind2/Ind3 in the etaAnab construction. -/
inductive IndHandling
  | ind1_integral_structure
  | ind2_kummer_vertical
  | ind3_upper_semi
  deriving DecidableEq, Repr

def indHandling : List IndHandling :=
  [.ind1_integral_structure, .ind2_kummer_vertical, .ind3_upper_semi]

theorem indHandling_length : (indHandling).length = 3 := rfl

/-- Ind3 exact upper-semi handling from the production vertical log-Kummer
contract: the hull dominates every transported Kummer image. -/
def ind3UpperSemi (K : VerticalLogKummerCorrespondence)
    (x₀ : K.F 0) (hull : K.D) : Prop :=
  K.HullDominates x₀ hull

/-- Exact missing Kummer vertical actual data.  Production has only the
conditional `VerticalLogKummerCorrespondence` contract; the concrete
log-shell/Frobenioid/Kummer construction is pending. -/
def kummerVerticalActual : Prop :=
  Nonempty (VerticalLogKummerCorrespondence.{u, u})

/-! ## Ind handling

- Ind1: the actual integral log-shell structure is fixed as `integralStructure`
  (`localShell.logShell`), not adjusted by a free Real;
- Ind2: the Kummer vertical layer is exactly the production
  `VerticalLogKummerCorrespondence` contract; its concrete inhabitant is the
  named gap `kummerVerticalActual_obligation`;
- Ind3: exact upper-semi handling is `ind3UpperSemi`, using
  `VerticalLogKummerCorrespondence.HullDominates`.

No direct Q/hull comparison is stated or used.
-/

end LeanFormal.IUT.N8Closure.EtaAnabLogShellActual
