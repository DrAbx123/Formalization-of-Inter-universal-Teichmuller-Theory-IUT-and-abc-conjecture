import tmp.sheaf.n8.closure.SourceLogKummerRealization
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel

/-!
# C2 actual finite-place log-Kummer data

Constructs `SourceLogKummerData I C1` from the production per-place donor
`sourceLocalLogShellDatum`, with zero sorry.  The data consists of the actual
local unit logarithm, its torsion kernel, the actual log-shell/pre-log-shell.

Not fields of `SourceLogKummerData`: G_v-invariant/action descent, actual
Kummer/root-change, K1/K2 boundary, archimedean branch, multi-place assembly.
Those remain downstream gaps and are not assumed here.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization

namespace LeanFormal.IUT.N8Closure.C2Actual

universe ua uv upi umon ui

/-- The actual C2 finite-place data for the production donor. -/
noncomputable def sourceLogKummerDataActual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I) :
    SourceLogKummerData I C1 where
  localShell := fun p _ place =>
    sourceLocalLogShellDatum (K := I.initial.arithmetic.Fmod) (p := p) place
  localShell_eq := by
    intro p _ place
    rfl
  kernel_eq_torsion := by
    intro p _ place
    exact unitLogHom_ker_eq_torsion (K := CommonPrimeCompletion
      (K := I.initial.arithmetic.Fmod) place) (p := p)
  logShell_eq := by
    intro p _ place
    exact sourceLocalLogShellDatum_logShell_eq_integralLogShell
      (K := I.initial.arithmetic.Fmod) (p := p) place
  preLogShell_eq := by
    intro p _ place
    exact sourceLocalLogShellDatum_preLogShell_eq_range_unitLogHom
      (K := I.initial.arithmetic.Fmod) (p := p) place

/-- C2 nonempty obligation, proved with no sorry. -/
theorem sourceLogKummerData_nonempty_actual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I) :
    Nonempty (SourceLogKummerData I C1) :=
  ⟨sourceLogKummerDataActual I C1⟩

theorem sourceLogKummerDataActual_localShell
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I) (p : Nat) [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) :
    (sourceLogKummerDataActual I C1).localShell p place =
      sourceLocalLogShellDatum (K := I.initial.arithmetic.Fmod) (p := p) place :=
  rfl

theorem sourceLogKummerDataActual_kernel
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I) (p : Nat) [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) :
    (unitLogHom (K := CommonPrimeCompletion
      (K := I.initial.arithmetic.Fmod) place) (p := p)).ker =
      CommGroup.torsion
        ((Integers (CommonPrimeCompletion
          (K := I.initial.arithmetic.Fmod) place))ˣ) :=
  unitLogHom_ker_eq_torsion (K := CommonPrimeCompletion
    (K := I.initial.arithmetic.Fmod) place) (p := p)

end LeanFormal.IUT.N8Closure.C2Actual