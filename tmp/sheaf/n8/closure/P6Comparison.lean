import tmp.sheaf.n8.closure.C9QPilotRegion
import tmp.sheaf.n8.closure.N8NativeClosure
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.SourceAlgorithmCompatibility
import tmp.sheaf.n8.closure.C6ActualIdentification
import tmp.sheaf.n8.closure.SourceThetaToIQ
import tmp.sheaf.n8.closure.C7Actual

/-!
# P6 comparison: source-allowed J versus native q

Exact P6 proposition (IUT III, xi-f / 10843-10898):

  exists a source-allowed output J such that
    (1) J is in HullPoss, and
    (2) ell_out(J) = Q,
  or the one-sided epsilon version
    forall epsilon > 0, exists J in HullPoss, Q - epsilon <= ell_out(J).

J is an actual output region associated to an actual C4 witnessed output
(C9ValuesPaper.outputRegion); its type does not mention Q, Q<=Theta, or the
desired equality.  Q is the actual native q-pilot scalar from C9QPilotRegion.
There is no Q<=Theta input anywhere in this file.

Source object existence is the only named obligation: the old-chain data
needed to form a source-allowed J (bridge/C2/C3/C4/C6/T11/witness) are not
constructed in production.  The P6 proposition itself is not asserted.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6Comparison

universe ua uv upi umon ui uL u_1

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

variable {l : PrimeGeFive}

/-- Paper label group over the actual finite signed-label set. -/
abbrev PaperLabel (l : PrimeGeFive) : Type :=
  Multiplicative (Additive (Equiv.Perm (SignedLabel l.value)))

/-- Actual native q-pilot scalar Q = -|log(q)| read from the native Clause (b) q. -/
noncomputable def QValue (X : N8NativeInput l) : ℝ :=
  qPilotSignedLog X

/-- A source-allowed output region J, formed from actual C4 witnessed output
data.  Its fields do not mention Q or Q<=Theta. -/
structure SourceAllowedOutput (X : N8NativeInput l) where
  /-- Missing old-chain bridge; this is the source object obligation. -/
  bridge : NativeOldC1Bridge X
  /-- Actual old C2 data. -/
  C2 : SourceLogKummerData bridge.input bridge.binding
  /-- Actual old C3 data. -/
  C3 : SourcePilotRegionData.{0, 0, 0, 0, 0, 0, 0} bridge.input
  /-- Actual old C4 witnessed output over the actual signed-label permutation
  group. -/
  D : SourceWitnessedOutputData bridge.input (PaperLabel l)
  /-- Actual T11 theta/IQ interface. -/
  T : SourceThetaIQInterface (I := bridge.input) C3
  /-- Measurability on the C3 tensor carrier. -/
  [measurableSpace : MeasurableSpace
    (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  /-- Borel structure on the C3 tensor carrier. -/
  [borelSpace : BorelSpace
    (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  /-- Actual C6 Haar measure. -/
  mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)
  /-- Actual C6 Haar instance. -/
  [addHaar : MeasureTheory.Measure.IsAddHaarMeasure mu]
  /-- Actual C6 IQ data. -/
  B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu
  /-- Procession index of the output witness. -/
  n : ThetaPilotCarrier l
  /-- Output state. -/
  x : bridge.input.ThetaPilotPoint D.place.v
  /-- Actual C4 witness retained as provenance. -/
  w : D.Witness n x

/-- Actual output region of a source-allowed J, independent of Q.  It is the
actual T11 theta-image set over the actual C4 choice family. -/
noncomputable def SourceAllowedOutput.region (J : SourceAllowedOutput X) :
    Set (C6IQCarrier J.C3.tensorPlaces J.C3.tensorTuple) :=
  {y | ∃ c : J.D.Choice J.n J.x, y = J.T.thetaImage J.n c}

/-- HullPoss: the source-allowed output region is contained in the actual C6
hull.  This is the admissibility condition; it does not involve Q. -/
def SourceAllowedOutput.hullPoss (J : SourceAllowedOutput X) : Prop := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  exact J.region ⊆ J.B.hull

/-- ell_out: the actual C6 normalized log-volume readout of J. -/
noncomputable def SourceAllowedOutput.ellOut (J : SourceAllowedOutput X) : ℝ := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  exact J.B.normalizedLogVolume J.region

/-- Exact P6: some source-allowed J is in HullPoss and has ell_out = Q.
The quantifier is over SourceAllowedOutput X only; Q appears only in the
right-hand equality. -/
def P6Exact (X : N8NativeInput l) (Q : ℝ) : Prop :=
  ∃ J : SourceAllowedOutput X, J.hullPoss ∧ J.ellOut = Q

/-- One-sided epsilon P6: for every epsilon > 0 there is a source-allowed J in
HullPoss with Q - epsilon <= ell_out(J). -/
def P6Epsilon (X : N8NativeInput l) (Q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ J : SourceAllowedOutput X, J.hullPoss ∧ Q - ε ≤ J.ellOut

/-- Exact P6 implies the epsilon version. -/
theorem p6Epsilon_of_p6Exact (X : N8NativeInput l) (Q : ℝ)
    (h : P6Exact X Q) : P6Epsilon X Q := by
  intro ε hε
  obtain ⟨J, hJ, hQ⟩ := h
  exact ⟨J, hJ, by linarith⟩

/-- The Q value used by P6 is the actual native q-pilot scalar; it is not
defined from Q<=Theta. -/
theorem QValue_eq_qPilotSignedLog (X : N8NativeInput l) :
    QValue X = qPilotSignedLog X := rfl

/-- Named source-object obligation: a source-allowed output J exists.  This is
the missing production source construction (old-chain bridge/C2/C3/C4/C6/T11
and witness); it is a component sorry, not an assumption on Q. -/
theorem sourceAllowedOutput_nonempty (X : N8NativeInput l) :
    Nonempty (SourceAllowedOutput X) := by
  sorry

end LeanFormal.IUT.N8Closure.P6Comparison
