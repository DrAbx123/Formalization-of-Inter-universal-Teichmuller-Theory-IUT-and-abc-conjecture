import tmp.sheaf.n8.closure.EtaKummerLogLink
import tmp.sheaf.n8.closure.C2Native
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCodomainClosure
import Mathlib

/-!
# ETA source log-shell datum: actual native construction

The actual native local log-shell datum is C2Native.nativeLocalShell.  Its
invariants are top, so the production theorem
SourceLogShellDatum.codomainKummerContained_of_invariants_eq_top gives the
Kummer-codomain containment without any dummy datum.

Thus the EtaKummerLogLink source-datum existential is actual.
-/

noncomputable section

namespace ABCBridge.N8.EtaKummerSourceDatumActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C2Native

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual native SourceLogShellDatum. -/
noncomputable abbrev etaSourceDatum : SourceLogShellDatum :=
  nativeLocalShell X

/-- The native datum has top invariants. -/
theorem etaSourceDatum_invariants (X : N8NativeInput l) :
    (etaSourceDatum X).invariants = ⊤ :=
  rfl

/-- Actual Kummer-codomain containment for the native datum. -/
theorem etaSourceDatum_codomainKummerContained (X : N8NativeInput l) :
    (etaSourceDatum X).codomainKummerContained :=
  SourceLogShellDatum.codomainKummerContained_of_invariants_eq_top
    (etaSourceDatum X) (etaSourceDatum_invariants X)

/-- The source-datum existential is actual (no dummy datum). -/
theorem etaKummerLogLinkSourceDatum_nonempty (X : N8NativeInput l) :
    ∃ D : SourceLogShellDatum.{0}, D.codomainKummerContained :=
  ⟨etaSourceDatum X, etaSourceDatum_codomainKummerContained X⟩

/-- The actual EtaKummerLogLink component package built from the native datum. -/
noncomputable def etaKummerLogLinkActual (X : N8NativeInput l) :
    EtaKummerLogLink.EtaKummerLogLinkActual :=
  EtaKummerLogLink.etaKummerLogLinkActualOfDatum
    (etaSourceDatum X) (etaSourceDatum_codomainKummerContained X)

end ABCBridge.N8.EtaKummerSourceDatumActual
