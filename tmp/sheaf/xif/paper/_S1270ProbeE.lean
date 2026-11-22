import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleOriginalInput
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActualTensorSpan
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import Mathlib.Data.Fin.Rev

noncomputable section
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace Probe1270E

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

abbrev ActualValuation : Type := {p : ℕ // p.Prime}

variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

def actualPlace : ActualValuation → Type ua :=
  fun vQ => FinitePlaceAtPrime I.initial.arithmetic.Fmod vQ.1

abbrev actualLocalLogShellDatum (vQ : ActualValuation) (v : actualPlace I vQ) :
    SourceLogShellDatum :=
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  sourceLocalLogShellDatum (p := vQ.1) v

abbrev actualIntegralLogShell (vQ : ActualValuation) (v : actualPlace I vQ) :
    AddSubgroup (CommonPrimeCompletion v) :=
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1)

noncomputable def actualLogShellFamily (j : Nat) :
    LogShellFamily.{0, 0, ua, ua} ℚ (actualPlace I) j where
  Shell := fun i vQ v => (actualLocalLogShellDatum I vQ v).IQSpan
  addCommMonoid := fun _ _ _ => inferInstance
  module := fun _ _ _ => inferInstance

theorem actualShell_mem_iff_span_integralLogShell
    (j : Nat) (i : Capsule j) (vQ : ActualValuation) (v : actualPlace I vQ)
    (x : CommonPrimeCompletion v) :
    x ∈ (actualLogShellFamily I j).Shell i vQ v ↔
      x ∈ Submodule.span ℚ (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) := by
  change x ∈ (actualLocalLogShellDatum I vQ v).IQSpan ↔ _
  rw [SourceLogShellDatum.IQSpan,
    sourceLocalLogShellDatum_logShell_eq_integralLogShell]
  rfl

theorem actualShell_eq_span_integralLogShell
    (j : Nat) (i : Capsule j) (vQ : ActualValuation) (v : actualPlace I vQ) :
    ((actualLogShellFamily I j).Shell i vQ v : Set (CommonPrimeCompletion v)) =
      (Submodule.span ℚ (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) :
        Set (CommonPrimeCompletion v)) := by
  ext x
  exact actualShell_mem_iff_span_integralLogShell I j i vQ v x

#print axioms actualShell_mem_iff_span_integralLogShell
#print axioms actualShell_eq_span_integralLogShell

end Probe1270E
