import tmp.sheaf.n8.closure.C9PaperClosure
import tmp.sheaf.n8.closure.P6ChainA
import tmp.sheaf.n8.closure.P6L

/-!
# C9 PaperC9Output source attempt (Wave19)

PaperC9Output has exactly three source fields:

  chainA : P6ChainAData X
  theta : P6Readout X mu
  valuesWitness : P6Readout X mu

The actual q scalar and Q are derived from chainA; Theta and Values are derived
from the readout object.  This file proves the exact component equivalence and
constructs the output from components.  The two external source gaps are:

  Nonempty (P6ChainAData X)  (actual route via GlobalLqDonor)
  Nonempty (P6Readout X mu)  (P6L readout gap)

No new field, no free source object, and no arbitrary q/Theta is introduced.
This is not a C10 assembly.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C9PaperOutputSourceAttempt

open LeanFormal.IUT
open MeasureTheory
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.C9PaperClosure

universe u

variable {l : PrimeGeFive} {X : N8NativeInput l}
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Actual PaperC9Output from components: one actual readout serves both Theta
and Values; no free Real/Set fields. -/
def paperC9OutputOfComponents
    (A : P6ChainAData X) (R : P6Readout (X := X) (mu := mu)) :
    PaperC9Output X mu where
  chainA := A
  theta := R
  valuesWitness := R

/-- Exact component equivalence for PaperC9Output existence. -/
theorem paperC9Output_nonempty_iff_components :
    Nonempty (PaperC9Output X mu) ↔
      Nonempty (P6ChainAData X) ∧
        Nonempty (P6Readout (X := X) (mu := mu)) := by
  constructor
  · rintro ⟨O⟩
    exact ⟨⟨O.chainA⟩, ⟨O.theta⟩⟩
  · rintro ⟨⟨A⟩, ⟨R⟩⟩
    exact ⟨paperC9OutputOfComponents A R⟩

/-- Actual construction from a GlobalLq donor and a global P6 readout. -/
def paperC9OutputOfGlobalLqReadout
    (D : GlobalLqDonor X) (R : P6Readout (X := X) (mu := mu)) :
    PaperC9Output X mu :=
  paperC9OutputOfComponents (p6ChainAOfGlobalLq X D) R

/-- Conditional existence from the two exact external sources. -/
theorem paperC9Output_nonempty_of_globalLq_readout
    (hD : Nonempty (GlobalLqDonor X))
    (hR : Nonempty (P6Readout (X := X) (mu := mu))) :
    Nonempty (PaperC9Output X mu) := by
  obtain ⟨D⟩ := hD
  obtain ⟨R⟩ := hR
  exact ⟨paperC9OutputOfGlobalLqReadout D R⟩

/-- Exact reduction to the P6L readout gap, using the named globalLq donor.
The local construction consumes the actual donor theorem; no new sorry. -/
theorem paperC9Output_nonempty_reduced
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] :
    Nonempty (PaperC9Output X mu) :=
  paperC9Output_nonempty_of_globalLq_readout
    (P6ChainA.globalLqDonor_nonempty X)
    (P6L.p6ReadoutExists_obligation (X := X) (mu := mu))

/-- Decisive no-go: PaperC9Output cannot be constructed from actual q/ChainA
alone.  The readout source is independent and is exactly the remaining external
obligation; a chainA-only construction would need a P6Readout. -/
theorem paperC9Output_requires_readout :
    Nonempty (PaperC9Output X mu) ->
      Nonempty (P6Readout (X := X) (mu := mu)) :=
  fun h => (paperC9Output_nonempty_iff_components.mp h).2

/-- The exact q scalar is derived, not stored: any output's Q is the native
q-pilot scalar. -/
theorem paperC9Output_Q_eq_nativeScalar (O : PaperC9Output X mu) :
    O.Q = qPilotSignedLog X :=
  PaperC9Output.Q_eq_nativeScalar O

end LeanFormal.IUT.N8Closure.C9PaperOutputSourceAttempt
