import tmp.sheaf.n8.closure.EtaFPlaceNormalizedComparison
import tmp.sheaf.n8.closure.EtaKummerLogLink
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCodomainClosure
import Mathlib

/-!
# ETA Kummer source datum at the native F-place

Audit correction: the ETA q/etaAnab object is at the native F-place, not the
old Fmod completion.  This file uses

  EtaFPlaceNormalizedComparison.fPlaceShell X

which is the production sourceLocalLogShellDatum at nativeFPlaceAtPrime X over
K = X.S.arithmetic.F.  Its invariants are top, so the production theorem
codomainKummerContained_of_invariants_eq_top gives the F-level Kummer-codomain
containment without any dummy datum and without using the Fmod shell.

No Fmod/F mixing is introduced.
-/

noncomputable section

namespace ABCBridge.N8.EtaKummerSourceDatumAtF

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.EtaKummerLogLink

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual F-place SourceLogShellDatum, not the Fmod shell. -/
noncomputable abbrev fSourceDatum : SourceLogShellDatum :=
  fPlaceShell X

/-- Its invariants are top. -/
theorem fSourceDatum_invariants (X : N8NativeInput l) :
    (fSourceDatum X).invariants = ⊤ :=
  rfl

/-- Actual F-level Kummer-codomain containment. -/
theorem fSourceDatum_codomainKummerContained (X : N8NativeInput l) :
    (fSourceDatum X).codomainKummerContained :=
  SourceLogShellDatum.codomainKummerContained_of_invariants_eq_top
    (fSourceDatum X) (fSourceDatum_invariants X)

/-- Actual F-level source-datum existential. -/
theorem etaKummerSourceDatumAtF_nonempty (X : N8NativeInput l) :
    ∃ D : SourceLogShellDatum.{0}, D.codomainKummerContained :=
  ⟨fSourceDatum X, fSourceDatum_codomainKummerContained X⟩

/-- The actual EtaKummerLogLink component package at the F-place. -/
noncomputable def etaKummerLogLinkActualAtF (X : N8NativeInput l) :
    EtaKummerLogLinkActual :=
  etaKummerLogLinkActualOfDatum
    (fSourceDatum X) (fSourceDatum_codomainKummerContained X)

end ABCBridge.N8.EtaKummerSourceDatumAtF
