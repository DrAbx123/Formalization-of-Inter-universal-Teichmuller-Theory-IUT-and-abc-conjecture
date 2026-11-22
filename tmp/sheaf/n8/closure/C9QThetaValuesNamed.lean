import tmp.sheaf.n8.closure.C9QPilotRegion
import tmp.sheaf.n8.closure.P6ChainA
import tmp.sheaf.n8.closure.P6ChainB
import tmp.sheaf.n8.closure.P6L

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# C9 Q/Theta/Values corrected named closure

Q is the actual Chain-A Real `P6ChainA.Q`, which is constrained by
`Q_eq_localScalar` to the actual native q scalar `qPilotSignedLog`.  Theta and
Values use the exact global source-object interfaces `P6L.P6Readout`; their
source-object existence is the visible gap and is stated by theorem-level
named sorries.  No singleton Values and no free Real field is introduced.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.P6L

namespace LeanFormal.IUT.N8Closure.C9QThetaValuesNamed

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual Theta source object: the global P6-L readout donor. -/
abbrev ThetaSourceObject
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] : Type _ :=
  P6L.P6Readout (X := X) (mu := mu)

/-- Actual Values source object: the same exact global readout donor; Values
are its `ellOut` images, not a stored set. -/
abbrev ValuesSourceObject
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] : Type _ :=
  P6L.P6Readout (X := X) (mu := mu)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Actual Q from Chain A; it is exactly the actual native q scalar. -/
def QNamed (C : P6ChainAData X) : ℝ := P6ChainA.Q (X := X) C

theorem QNamed_eq_nativeScalar (C : P6ChainAData X) :
    QNamed X C = qPilotSignedLog X := by
  calc
    QNamed X C = C.localData.scalar := by
      change C.Q = C.localData.scalar
      exact P6ChainA.Q_eq_localScalar (X := X) C
    _ = qPilotSignedLog X := C.localData.scalar_eq

/-- Actual Theta readout value from an exact source object. -/
def ThetaNamed (R : ThetaSourceObject (X := X) mu) : ℝ :=
  R.ellOutValue

/-- Values as the set of actual `ellOut` readouts; not a singleton and no
stored Real. -/
def ValuesNamed : Set ℝ :=
  {z | ∃ R : ValuesSourceObject (X := X) mu, z = R.ellOutValue}

theorem mem_ValuesNamed_iff (z : ℝ) :
    z ∈ ValuesNamed (X := X) mu ↔
      ∃ R : ValuesSourceObject (X := X) mu, z = R.ellOutValue := Iff.rfl

/-- Exact missing Q source donor: the global L_q readout. -/
def MissingQSource : Prop := Nonempty (GlobalLqDonor X)

/- The theorem `missing_q_source` is intentionally absent: no source-valid
   `GlobalLqDonor` is constructed in the tree. The only formal inhabitant is the
   underconstrained constant donor, which is not the paper source readout and is
   excluded as fake/toy. See C9-NOSORRY-QTHETA-20261025.md for the exact
   obstruction. -/

/-- Exact missing Theta source object. -/
def MissingThetaSource : Prop :=
  Nonempty (ThetaSourceObject (X := X) mu)

/- The theorem `missing_theta_source` is intentionally absent: P6Readout is the
   named global readout obligation, not a constructed source object. Under an
   archimedean native place the frozen P6Readout is in fact refuted by
   P6AdmRedesign.frozenP6Readout_impossible_of_archimedean_at. See
   C9-NOSORRY-QTHETA-20261025.md for the exact obstruction. -/

/-- Exact missing Values source object. -/
def MissingValuesSource : Prop :=
  Nonempty (ValuesSourceObject (X := X) mu)

/- The theorem `missing_values_source` is intentionally absent: Values are the
   `ellOut` images of the same missing P6Readout donor; no source object is
   constructed. See C9-NOSORRY-QTHETA-20261025.md for the exact obstruction. -/

end LeanFormal.IUT.N8Closure.C9QThetaValuesNamed

end