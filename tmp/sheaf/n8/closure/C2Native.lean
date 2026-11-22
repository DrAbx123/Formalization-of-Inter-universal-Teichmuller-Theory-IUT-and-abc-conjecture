import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.n8.closure.C2Actual
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellXMuPacket
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActionCompatibility
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogKummerK1K2

/-!
# C2 native local log/Kummer/K1K2/action slice

Builds the actual native finite-place local log data from the native source and
strip slice of C1 (NativeC1), using the production `sourceLocalLogShellDatum`.
This is a new native slice, not the old `SourceLogKummerData` full-C2 claim.

The old finite-place `SourceLogKummerData` donor is kept separately (imported
from C2Actual) but is not treated as the full C2 object.

Missing production declarations are recorded explicitly at the end: there is no
native C1-indexed G_v action/descent type, no native Kummer/root-change map,
no native multi-place K1/K2 boundary, and no native archimedean branch.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm

namespace LeanFormal.IUT.N8Closure.C2Native

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- A bad finite base place selected from native nonemptiness. -/
noncomputable def badBasePlace : NumberField.FinitePlace X.S.arithmetic.Fmod :=
  Classical.choose (show ∃ x, x ∈ X.S.tuple.source.V_mod_bad from
    X.S.tuple.source.V_mod_bad_nonempty)

theorem badBasePlace_mem :
    badBasePlace X ∈ X.S.tuple.source.V_mod_bad :=
  Classical.choose_spec (show ∃ x, x ∈ X.S.tuple.source.V_mod_bad from
    X.S.tuple.source.V_mod_bad_nonempty)

/-- The corresponding selected K-place, finite over the bad base place. -/
noncomputable def badPlace : NativePlaces X.S :=
  X.S.tuple.source.V_mod_bijection (NumberFieldPlace.finite (badBasePlace X))

theorem badPlace_comap :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) (badPlace X).1 =
      NumberFieldPlace.finite (badBasePlace X) := by
  have h : X.S.tuple.source.V_mod_bijection.symm (badPlace X) =
      NumberFieldPlace.finite (badBasePlace X) := by
    unfold badPlace
    rw [Equiv.symm_apply_apply]
  exact (X.S.tuple.source.V_place_comap (badPlace X)).trans h

/-- Prime below the native bad finite base place. -/
noncomputable abbrev badPrime : Nat.Primes :=
  completionRationalPrime (badBasePlace X)

local instance badPrimeFact : Fact (Nat.Prime (badPrime X).val) :=
  ⟨(badPrime X).property⟩

/-- The native bad base place as a prime-indexed finite place. -/
noncomputable def badPlaceAtPrime :
    FinitePlaceAtPrime (X.S.arithmetic.Fmod) (badPrime X).val :=
  ⟨badBasePlace X, rfl⟩

/-- Actual native local log-shell donor at the bad finite base place. -/
noncomputable def nativeLocalShell : SourceLogShellDatum :=
  sourceLocalLogShellDatum (K := X.S.arithmetic.Fmod) (p := (badPrime X).val)
    (badPlaceAtPrime X)

theorem nativeLocalShell_kernel_eq_torsion :
    (unitLogHom (K := CommonPrimeCompletion (K := X.S.arithmetic.Fmod)
      (badPlaceAtPrime X)) (p := (badPrime X).val)).ker =
      CommGroup.torsion
        ((Integers (CommonPrimeCompletion (K := X.S.arithmetic.Fmod)
          (badPlaceAtPrime X)))ˣ) :=
  unitLogHom_ker_eq_torsion (K := CommonPrimeCompletion
    (K := X.S.arithmetic.Fmod) (badPlaceAtPrime X)) (p := (badPrime X).val)

theorem nativeLocalShell_logShell_eq :
    (nativeLocalShell X).logShell =
      (integralLogShell (K := CommonPrimeCompletion (K := X.S.arithmetic.Fmod)
        (badPlaceAtPrime X)) (p := (badPrime X).val) :
        Set (CommonPrimeCompletion (K := X.S.arithmetic.Fmod)
          (badPlaceAtPrime X))) :=
  sourceLocalLogShellDatum_logShell_eq_integralLogShell
    (K := X.S.arithmetic.Fmod) (p := (badPrime X).val) (badPlaceAtPrime X)

theorem nativeLocalShell_preLogShell_eq :
    (nativeLocalShell X).preLogShell =
      Multiplicative.toAdd '' Set.range
        (unitLogHom (K := CommonPrimeCompletion (K := X.S.arithmetic.Fmod)
          (badPlaceAtPrime X)) (p := (badPrime X).val)) :=
  sourceLocalLogShellDatum_preLogShell_eq_range_unitLogHom
    (K := X.S.arithmetic.Fmod) (p := (badPrime X).val) (badPlaceAtPrime X)

/-- The actual native log slice: bad finite base place, native K-place, and
the actual local log-shell donor.  Kernel/shell equalities are the separate
theorems above. -/
structure NativeLogSlice where
  basePlace : NumberField.FinitePlace (X.S.arithmetic.Fmod)
  basePlace_mem : basePlace ∈ X.S.tuple.source.V_mod_bad
  nativePlace : NativePlaces X.S
  nativePlace_comap :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) nativePlace.1 =
      NumberFieldPlace.finite basePlace
  localShell : SourceLogShellDatum

noncomputable def nativeLogSlice : NativeLogSlice X where
  basePlace := badBasePlace X
  basePlace_mem := badBasePlace_mem X
  nativePlace := badPlace X
  nativePlace_comap := badPlace_comap X
  localShell := nativeLocalShell X
/- The old finite-place `SourceLogKummerData` donor remains conditional and
is not the full C2 object; it is kept for downstream finite-place consumers. -/
#check LeanFormal.IUT.N8Closure.C2Actual.sourceLogKummerDataActual

/-! ## Exact missing production declarations

No production declaration currently supplies the following native C1-indexed
pieces:

1. native G_v action/action descent: the only action type is the conditional
   `SourceLogShellXMuChainActionCompatibility` over `D X F G S`, not a native
   C1-indexed action constructed from `N8NativeInput`;
2. native Kummer/root-change map: `SourceLogShellDatum.codomainKummerContained`
   is only a Prop and `SourceLogShellXMuPacket` is a conditional chain supply;
3. native multi-place K1/K2 boundary: `LogKummerK1K2`/Consumer are per-
   completion consumers, not a native multi-place boundary;
4. native archimedean branch: no native archimedean source object is present in
   `N8NativeInput`/`NativeC1`.

These are exact no-go declarations, not fields of `NativeLogSlice` and not
assumed hypotheses.
-/
#check LeanFormal.IUT.SourceLogShellXMuChainActionCompatibility
#check LeanFormal.IUT.SourceLogShellDatum.codomainKummerContained
#check ABCBridge.LogKummerK1K2.principalUnitMap

end LeanFormal.IUT.N8Closure.C2Native
