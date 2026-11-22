import tmp.sheaf.n8.closure.P6L
import tmp.sheaf.n8.closure.P6ChainA
import tmp.sheaf.n8.closure.P6ChainB

/-!
# P6-L closure: global L/Adm readout + Chain A/B source existence

Reuses P6L global signed procession-normalized `ellOut`, Adm regions and
`P6Readout`; ties the P6 readout to P6ChainA (native q -> L_q -> Q) and
P6ChainB (complete alpha/R_alpha).  The source existence/gap is exactly the
named-sorry obligation; no old L0.5 target and no single-block
normalizedLogVolume are used.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.P6ChainB

namespace LeanFormal.IUT.N8Closure.P6LClosure

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

variable {V : Type uv} {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable (D : SourceWitnessedOutputData (l := l) (V := V) I Label)

/-- Exact P6 source gap: the global P6 readout, Chain A's global L_q donor,
and Chain B's S/L -> complete-alpha construction.  All three types are
existing P6L/P6ChainA/P6ChainB targets; nothing is redefined. -/
def P6LSourceGap : Prop :=
  Nonempty (P6Readout (X := X) (mu := mu)) ∧
  Nonempty (GlobalLqDonor X) ∧
  MissingSLToCompleteAlpha.{ua, upi, umon, ui} X

/-- Assembled P6-L closure: global readout plus Chain A and Chain B data.
Every field is an existing actual interface type; no free Real/Set field. -/
structure P6LSourceClosure where
  readout : P6Readout (X := X) (mu := mu)
  chainA : P6ChainAData X
  chainB : CompleteAlpha (D := D)

/-- Actual constructor from already supplied readout/Chain A/Chain B data. -/
def P6LSourceClosure.ofData
    (readout : P6Readout (X := X) (mu := mu))
    (chainA : P6ChainAData X)
    (chainB : CompleteAlpha (D := D)) :
    P6LSourceClosure (X := X) (mu := mu) (D := D) where
  readout := readout
  chainA := chainA
  chainB := chainB

/-- The global readout value of the assembled closure is the P6L ellOut value. -/
theorem P6LSourceClosure.readout_value_eq
    (C : P6LSourceClosure (X := X) (mu := mu) (D := D)) :
    C.readout.value =
      ellOut (X := X) (mu := mu) C.readout.support C.readout.weight
        C.readout.dimension C.readout.reference C.readout.region :=
  C.readout.value_eq

/-- Chain A Q of the assembled closure is exactly the P6ChainA Q. -/
theorem P6LSourceClosure.chainA_Q_eq
    (C : P6LSourceClosure (X := X) (mu := mu) (D := D)) :
    C.chainA.Q = C.chainA.Q := rfl

/-- Chain B complete alpha of the closure has its actual R_alpha region. -/
theorem P6LSourceClosure.chainB_RAlpha_eq
    (C : P6LSourceClosure (X := X) (mu := mu) (D := D)) :
    RAlpha (D := D) C.chainB = D.U C.chainB.n C.chainB.x := rfl

end LeanFormal.IUT.N8Closure.P6LClosure
