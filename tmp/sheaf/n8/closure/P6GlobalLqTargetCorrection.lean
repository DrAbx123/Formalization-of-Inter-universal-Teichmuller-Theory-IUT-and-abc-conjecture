import tmp.sheaf.n8.closure.P6ChainA
import tmp.sheaf.n8.closure.P6L
import tmp.sheaf.n8.closure.P6GlobalLqDonorUnderconstrained
import tmp.sheaf.n8.closure.C9PaperClosure

/-!
# P6 GlobalLq target correction (Wave21)

Wave20 showed GlobalLqDonor is underconstrained: a constant readout with the
one-point equality inhabits it.  This file records the corrected target.

SourceGlobalLqDonor requires an actual global P6Readout together with the exact
value identification

  readout.ellOutValue = qPilotSignedLog X.

It contains no free global-L function/Real field.  The corrected target is
Nonempty SourceGlobalLqDonor, a named source gap.  A constant GlobalLqDonor is
only a formal readout interface; it is not source evidence.

Consumers:
- C9QThetaValuesNamed.MissingQSource / missing_q_source are NOT discharged by
  the constant donor; the corrected consumer must use
  SourceGlobalLqDonor (or state source correctness explicitly).
- C9PaperClosure.PaperC9Output built from the constant GlobalLqDonor is not
  source-correct; C9PaperOutputSourceCorrected gates it by the corrected target.

No owner file is edited and no free L data is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6GlobalLqTargetCorrection

open LeanFormal.IUT
open MeasureTheory
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.P6GlobalLqDonorUnderconstrained

universe u

variable {l : PrimeGeFive} {X : N8NativeInput l}
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Corrected source global L_q target: an actual global P6 readout whose value
is exactly the native q-pilot scalar.  No free global-L function is added. -/
structure SourceGlobalLqDonor (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] where
  /-- Actual global P6 readout. -/
  readout : P6Readout (X := X) (mu := mu)
  /-- Source value identification with the native q scalar. -/
  value_eq : readout.ellOutValue = qPilotSignedLog X

/-- Corrected target proposition. -/
def SourceGlobalLqTarget
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] : Prop :=
  Nonempty (SourceGlobalLqDonor X mu)

/-- A corrected source gives an actual formal GlobalLqDonor (constant on
P6ChainALocal), not the reverse. -/
def SourceGlobalLqDonor.toFormal
    (S : SourceGlobalLqDonor X mu) : GlobalLqDonor X where
  readout := fun _ => S.readout.ellOutValue
  readout_eq_local := S.value_eq

/-- Every corrected source yields an actual P6Readout. -/
theorem SourceGlobalLqDonor.hasReadout
    (S : SourceGlobalLqDonor X mu) :
    Nonempty (P6Readout (X := X) (mu := mu)) :=
  ⟨S.readout⟩

/-- Corrected C9 paper output consumer: a PaperC9Output plus actual corrected
global L_q source.  Constant formal donor alone is not accepted. -/
structure C9PaperOutputSourceCorrected
    (O : C9PaperClosure.PaperC9Output X mu) where
  source : SourceGlobalLqDonor X mu

/-- Corrected target nonempty iff the source gap is supplied. -/
theorem c9PaperOutputSourceCorrected_nonempty
    (O : C9PaperClosure.PaperC9Output X mu)
    (h : SourceGlobalLqTarget X mu) :
    Nonempty (C9PaperOutputSourceCorrected O) := by
  obtain ⟨S⟩ := h
  exact ⟨{ source := S }⟩

end LeanFormal.IUT.N8Closure.P6GlobalLqTargetCorrection
