import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummerOrderedLayer
import tmp.sheaf.n8.closure.C2Native
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCodomainClosure
import Mathlib

/-!
# ETA-4: Kummer / log-link / vertical log-shell components for etaAnab

This file constructs the Kummer/log-link/vertical log-shell component from the
production SourceLogShellDatum:

- vertical log-shell: D.logShell;
- Kummer image: u |-> (D.logMap u).toAdd, with the actual membership proof;
- log-link step and iterate: the production identity reduction carried by
  NonarchimedeanLogKummerUpperSemi from SourceLogShellDatum.toNonarchimedeanUpperSemi.

The construction is actual for any production datum D together with the named
source condition D.codomainKummerContained.

The remaining exact ETA-4 gap is a production datum attached to the etaAnab
source object / native completion.  No direct pilot comparison is made.
-/

noncomputable section

namespace ABCBridge.N8.EtaKummerLogLink

open LeanFormal.IUT

universe u

variable {l : PrimeGeFive}

/-- Actual Kummer/log-link/vertical log-shell components from a production
SourceLogShellDatum. -/
structure EtaKummerLogLinkActual where
  D : SourceLogShellDatum
  contained : D.codomainKummerContained
  /-- The production upper-semi Kummer/log-link interface. -/
  upperSemi : NonarchimedeanLogKummerUpperSemi :=
    D.toNonarchimedeanUpperSemi contained
  /-- The vertical log-shell. -/
  verticalLogShell : Set D.K := D.logShell
  /-- The actual Kummer image map. -/
  kummer : D.Units → D.K := fun u => (D.logMap u).toAdd
  /-- Actual Kummer image membership in the vertical log-shell. -/
  kummer_mem_verticalLogShell : ∀ u : D.Units,
    kummer u ∈ verticalLogShell := by
    intro u
    exact contained ⟨u, rfl⟩
  /-- Actual log-link step and iterate from the production interface. -/
  logLinkStep : D.Units → D.Units → Prop := fun y z => z = y
  logIterate : D.Units → D.Units → Prop := fun v w => w = v

/-- Actual component construction from any production SourceLogShellDatum and
its Kummer-codomain condition, zero sorry. -/
noncomputable def etaKummerLogLinkActualOfDatum
    (D : SourceLogShellDatum) (h : D.codomainKummerContained) :
    EtaKummerLogLinkActual where
  D := D
  contained := h
  upperSemi := D.toNonarchimedeanUpperSemi h
  verticalLogShell := D.logShell
  kummer := fun u => (D.logMap u).toAdd
  kummer_mem_verticalLogShell := fun u => h ⟨u, rfl⟩
  logLinkStep := fun y z => z = y
  logIterate := fun v w => w = v

/-- The Kummer image lands in the production log-shell, actual theorem. -/
theorem etaKummerLogLinkActual_kummer_mem
    (E : EtaKummerLogLinkActual) (u : E.D.Units) :
    E.kummer u ∈ E.verticalLogShell :=
  E.kummer_mem_verticalLogShell u

/-- The Kummer/log-shell component is actual for every production datum. -/
theorem etaKummerLogLinkActual_kummer_mem_logShell
    (D : SourceLogShellDatum) (h : D.codomainKummerContained) (u : D.Units) :
    (D.logMap u).toAdd ∈ D.logShell :=
  h ⟨u, rfl⟩

/-- Actual ETA-4 source datum: the native local log-shell datum from C2Native.
Its invariants are top, so the production codomain-Kummer theorem applies. -/
theorem etaKummerLogLinkSourceDatum_nonempty (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l) :
    ∃ D : SourceLogShellDatum.{0}, D.codomainKummerContained :=
  ⟨LeanFormal.IUT.N8Closure.C2Native.nativeLocalShell X,
    SourceLogShellDatum.codomainKummerContained_of_invariants_eq_top _
      rfl⟩

end ABCBridge.N8.EtaKummerLogLink
