import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# P6 Chain B: S/L -> complete alpha -> R_alpha -> U/H

Exact stage-2 chain types.  `CompleteAlpha` and `RAlpha` are built from the
actual C4 dependent-pair choice/output data, not from free Set/Real fields.
Raw pre-region (`rawPreRegion`, the actual finite C4 output set) is kept
distinct from the component union `componentUnion` and from the enlarged
source hull `enlargedHull` (`sourceHolomorphicHull`).

The missing S/L -> complete-alpha source construction is the named
`missing_sl_to_complete_alpha` obligation.  The only needed first donor is a
`NativeOriginalInputDonors X`; no free alpha/region field is introduced.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open ABCBridge.N8.C4Actual

namespace LeanFormal.IUT.N8Closure.P6ChainB

universe ua uv upi umon ui uL

variable {l : PrimeGeFive}
  {V : Type uv}
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
  {Label : Type uL} [Group Label]
  (D : SourceWitnessedOutputData (l := l) (V := V) I Label)

/-- An actual complete alpha choice: procession, output state and the actual
C4 dependent-pair choice.  No free region or Real field. -/
structure CompleteAlpha where
  /-- Procession label. -/
  n : ThetaPilotCarrier l
  /-- Output state. -/
  x : I.ThetaPilotPoint D.place.v
  /-- Actual complete C4 choice at that output state. -/
  choice : D.Choice n x

/-- The raw pre-region: the actual finite C4 output set at `(n,x)`. -/
def rawPreRegion (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint D.place.v) : Set (I.ThetaPilotPoint D.place.v) :=
  D.U n x

/-- The component region `R_alpha` associated to an actual complete alpha:
the actual output region at its procession/state. -/
def RAlpha (a : CompleteAlpha (D := D)) : Set (I.ThetaPilotPoint D.place.v) :=
  D.U a.n a.x

/-- The component union `U` over a set of actual complete alpha choices. -/
def componentUnion (A : Set (CompleteAlpha (D := D))) :
    Set (I.ThetaPilotPoint D.place.v) :=
  {y | ∃ a ∈ A, y ∈ RAlpha (D := D) a}

/-- The enlarged hull `H`: the actual source holomorphic hull, not the raw
pre-region and not the component union. -/
def enlargedHull (n : ThetaPilotCarrier l) :
    Set (I.ThetaPilotPoint D.place.v) :=
  (I.sourceHolomorphicHull D.place.v D.place.R n : Set (I.ThetaPilotPoint D.place.v))

/-- The raw pre-region is contained in the enlarged source hull: its points
are actual theta-pilot outputs and the source hull contains all such images. -/
theorem rawPreRegion_subset_enlargedHull
    (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v) :
    rawPreRegion (D := D) n x ⊆ enlargedHull (D := D) n := by
  intro y hy
  rw [rawPreRegion, D.U_eq_possibleImage] at hy
  rcases hy with ⟨c, rfl⟩
  exact I.sourceThetaPilotPoint_mem_sourceHolomorphicHull D.place.v D.place.R n c

/-- The exact missing S/L -> complete-alpha source construction. -/
def MissingSLToCompleteAlpha (X : N8NativeInput l) : Prop :=
  Nonempty (OriginalInput.{ua, 0, upi, umon, ui} l (NativePlaces X.S))

theorem missing_sl_to_complete_alpha (X : N8NativeInput l) :
    MissingSLToCompleteAlpha X := by
  sorry

end LeanFormal.IUT.N8Closure.P6ChainB

end