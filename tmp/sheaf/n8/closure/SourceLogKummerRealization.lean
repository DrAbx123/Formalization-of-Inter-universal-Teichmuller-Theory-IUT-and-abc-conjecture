import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import tmp.sheaf.n8.closure.SourceInputBinding
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel

/-!
# C2 stage 2 — SourceLogKummerData (finite-place actual log data)

Parameters: `I : OriginalInput l V` and the accepted C1 `C1 : SourceInputBinding I`.

This structure records only actual finite-place data that already has a real
Lean type.  The local log shell is forced to be the production donor
`sourceLocalLogShellDatum`; kernel is the actual torsion kernel; log-shell and
pre-log-shell are the actual integral log-shell/range.  No free `K`, `Units`,
`invariants`, `logMap`, Kummer arrow, action descent or K1/K2 boundary is a
field.

Still missing and therefore NOT fields: actual G_v-invariant submonoid/action
descent, actual Kummer/root-change map, K1/K2 connection, archimedean branch,
and the C1 place-indexed multi-place assembly (C1 currently gives a place
equivalence, not a completion-indexed family).  These are named gaps in C2Actual.

The actual C2 inhabitant is now constructed in C2Actual.lean
(sourceLogKummerDataActual / sourceLogKummerData_nonempty_actual); this file
keeps only the structure definition.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.SourceLogKummerRealization

universe ua uv upi umon ui u

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourceInputBinding

variable {l : PrimeGeFive} {V : Type uv}

/-- C2 finite-place data.  `localShell` is constrained by equality to the
actual donor `sourceLocalLogShellDatum`; the other fields are the actual
kernel/log-shell facts for the same completion. -/
structure SourceLogKummerData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I) where
  /-- Actual per-finite-place log-shell carrier. -/
  localShell : ∀ (p : Nat) [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p),
    SourceLogShellDatum
  /-- The carrier is the actual donor, not a freely chosen datum. -/
  localShell_eq : ∀ (p : Nat) [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p),
    localShell p place =
      sourceLocalLogShellDatum (K := I.initial.arithmetic.Fmod) (p := p) place
  /-- The actual unit logarithm has kernel exactly the torsion subgroup. -/
  kernel_eq_torsion : ∀ (p : Nat) [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p),
    (unitLogHom (K := CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
      (p := p)).ker =
      CommGroup.torsion
        ((Integers (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))ˣ)
  /-- The actual log-shell is the integral log-shell of the completion. -/
  logShell_eq : ∀ (p : Nat) [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p),
    (sourceLocalLogShellDatum (K := I.initial.arithmetic.Fmod) (p := p) place).logShell =
      (integralLogShell
        (K := CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
        (p := p) : Set (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))
  /-- The pre-log-shell is the additive image of the actual unit-log range. -/
  preLogShell_eq : ∀ (p : Nat) [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p),
    (sourceLocalLogShellDatum (K := I.initial.arithmetic.Fmod) (p := p) place).preLogShell =
      Multiplicative.toAdd '' Set.range
        (unitLogHom
          (K := CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
          (p := p))



end LeanFormal.IUT.N8Closure.SourceLogKummerRealization