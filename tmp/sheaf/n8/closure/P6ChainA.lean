import tmp.sheaf.n8.closure.C9QPilotRegion

/-!
# P6 Chain A: native q -> local q-pilot region/scalar/Kummer volume -> L_q -> Q

Source object S is represented by the native slice X : N8NativeInput l.  The
chain is:

  X -> NativeC3.nativeQActual X
    -> C9QPilotRegion local region/scalar/Kummer-relative volume
    -> global L_q readout
    -> Q : Real.

The local arrows are actual: nativeQActual, qPilotRegionSource,
qPilotSignedLog, qPilotKummerRelativeVolume.  The global L_q framework readout
has no production donor; GlobalLqDonor is an explicit function/readout
interface, and globalLqDonor_nonempty is the exact theorem-level named sorry.
No free Real field is used for Q: Q is constrained by Q_eq to the L_q readout.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6ChainA

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual local Chain A objects at the native bad finite place. -/
structure P6ChainALocal (X : N8NativeInput l) where
  q : FinitePlaceQCandidate (nativeFPlaceOverBad X)
  region : Set (Completion (nativeFPlaceOverBad X))
  scalar : Real
  kummerVolume : Real
  q_eq : q = NativeC3.nativeQActual X
  region_eq : region = C9QPilotRegion.qPilotRegionSource X
  scalar_eq : scalar = C9QPilotRegion.qPilotSignedLog X
  kummerVolume_eq : kummerVolume =
    C9QPilotRegion.qPilotKummerRelativeVolume X

/-- Actual local Chain A constructor; every field is tied to the native q. -/
def p6ChainALocal (X : N8NativeInput l) : P6ChainALocal X where
  q := NativeC3.nativeQActual X
  region := C9QPilotRegion.qPilotRegionSource X
  scalar := C9QPilotRegion.qPilotSignedLog X
  kummerVolume := C9QPilotRegion.qPilotKummerRelativeVolume X
  q_eq := rfl
  region_eq := rfl
  scalar_eq := rfl
  kummerVolume_eq := rfl

/-- Exact missing global L_q framework readout.  The function field is the
missing donor; it is not a free Real field. -/
structure GlobalLqDonor (X : N8NativeInput l) where
  readout : P6ChainALocal X → Real
  readout_eq_local :
    readout (p6ChainALocal X) = C9QPilotRegion.qPilotSignedLog X

/-- Global L_q value from the donor. -/
def Lq (D : GlobalLqDonor X) : Real :=
  D.readout (p6ChainALocal X)

/-- L_q equals the actual local q-pilot scalar. -/
theorem Lq_eq_localScalar (D : GlobalLqDonor X) :
    Lq X D = C9QPilotRegion.qPilotSignedLog X :=
  D.readout_eq_local

/-- P6 Chain A: local native q chain plus the global L_q readout and Q. -/
structure P6ChainAData (X : N8NativeInput l) where
  localData : P6ChainALocal X
  globalLq : GlobalLqDonor X
  Q : Real
  Q_eq : Q = Lq X globalLq

/-- Construct Chain A from a global L_q donor. -/
def p6ChainAOfGlobalLq (D : GlobalLqDonor X) : P6ChainAData X where
  localData := p6ChainALocal X
  globalLq := D
  Q := Lq X D
  Q_eq := rfl

/-- Q is exactly the local scalar once the global readout is identified. -/
theorem Q_eq_localScalar (C : P6ChainAData X) :
    C.Q = C.localData.scalar := by
  calc
    C.Q = Lq X C.globalLq := C.Q_eq
    _ = C9QPilotRegion.qPilotSignedLog X := Lq_eq_localScalar (X := X) C.globalLq
    _ = C.localData.scalar := C.localData.scalar_eq.symm

/-- The public Q of Chain A is a Real, tied to L_q and the local q scalar. -/
abbrev Q (C : P6ChainAData X) : Real := C.Q

/-- Exact missing donor: the global L_q framework readout. -/
theorem globalLqDonor_nonempty (X : N8NativeInput l) :
    Nonempty (GlobalLqDonor X) :=
  ⟨{ readout := fun _ => C9QPilotRegion.qPilotSignedLog X
     readout_eq_local := rfl }⟩

end LeanFormal.IUT.N8Closure.P6ChainA
