import tmp.sheaf.n8.closure.P6ChainA
import tmp.sheaf.n8.closure.P6ChainB
import tmp.sheaf.n8.closure.P6Hull
import tmp.sheaf.n8.closure.P6L
import tmp.sheaf.n8.closure.P6SHEInd
import tmp.sheaf.n8.closure.P6Tensor
import tmp.sheaf.n8.closure.P6Indices
import tmp.sheaf.n8.closure.P6Comparison
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.SourceInputBinding
import tmp.sheaf.n8.closure.SourceLogKummerRealization
import tmp.sheaf.n8.closure.SourcePilotRegion

/-!
# C9 P6 closure — assembly of the existing P6 components

This file only assembles the component types:

- P6ChainA: native q -> local q-pilot objects -> L_q -> Q;
- P6ChainB: actual complete alpha and R_alpha;
- P6Hull: paper hull/HullPoss package;
- P6L: global ell_out/readout;
- P6SHEInd: SHE/Ind data;
- P6Tensor: C3 tensor/landing output;
- P6Indices: S/L/alpha component indices;
- P6Comparison: source-allowed J, P6Exact/P6Epsilon, Q.

P6SourceClosure is a structure over those components.  The comparison field is
one of the source Propositions P6Exact/P6Epsilon; its J range is
SourceAllowedOutput X, which does not mention Q <= Theta.  Source existence is a
single theorem-level named sorry (p6SourceClosure_nonempty).

No component is redefined here and no free Real/Set is introduced by this file.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C9P6Closure

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.P6Comparison

universe ua uv upi umon ui uL uG uI uVp

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {LAdd : Type uG} [AddGroup LAdd]
variable (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (X : N8NativeInput l)
variable (T : P6Indices.TupleIndex X)
variable (Dq : NativeQDonor X)
variable (Lt : P6Tensor.P6TensorLandingData X)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]

/-- Assembled P6 source closure over the existing component types. -/
structure P6SourceClosure
    (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
    (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (X : N8NativeInput l) (T : P6Indices.TupleIndex X)
    (Dq : NativeQDonor X) (Lt : P6Tensor.P6TensorLandingData X)
    [hNorm : forall v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [hMeas : forall v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [hBorel : forall v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : forall v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [hHaar : forall v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] where
  /-- Chain A: native q -> local q-pilot -> L_q -> Q. -/
  chainA : P6ChainA.P6ChainAData X
  /-- Chain B: an actual complete alpha choice. -/
  chainB : P6ChainB.CompleteAlpha (D := D)
  /-- Paper hull/HullPoss package. -/
  hull : P6Hull.P6HullSetup.{uv, uI}
  /-- Global ell_out/readout. -/
  readout : P6L.P6Readout (X := X) (mu := mu)
  /-- SHE/Ind data. -/
  sheInd : P6SHEInd.P6FullData I C1 C2 C3 D
  /-- C3 -> tensor/landing output. -/
  tensor : P6Tensor.P6C3TensorOutput (X := X) Dq Lt
  /-- S/L/alpha component index. -/
  alphaIndex : P6Indices.AlphaIndex X T
  /-- Exact or epsilon P6 comparison.  J ranges over SourceAllowedOutput X only. -/
  comparison : P6Comparison.P6Exact X chainA.Q ∨ P6Comparison.P6Epsilon X chainA.Q
  /-- Named source existence: an actual source-allowed output J. -/
  sourceExists : Nonempty (P6Comparison.SourceAllowedOutput X)

/-- Q of the assembled closure is exactly Chain A's Q. -/
abbrev P6SourceClosure.Q
    [hNorm : forall v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [hMeas : forall v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [hBorel : forall v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : forall v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [hHaar : forall v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (C : P6SourceClosure D C1 C2 C3 X T Dq Lt mu) : Real := C.chainA.Q

/-- The comparison's J range is independent of Q <= Theta: it is exactly
SourceAllowedOutput X. -/
def ComparisonJRanges (X : N8NativeInput l) : Set (Type _) :=
  {Y | Y = P6Comparison.SourceAllowedOutput X}

/-- Named source existence for the assembled closure.  The only missing input
is the actual source-object construction; no Q <= Theta input is used. -/
theorem p6SourceClosure_nonempty
    (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
    (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (X : N8NativeInput l) (T : P6Indices.TupleIndex X)
    (Dq : NativeQDonor X) (Lt : P6Tensor.P6TensorLandingData X)
    [hNorm : forall v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [hMeas : forall v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [hBorel : forall v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : forall v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [hHaar : forall v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] :
    Nonempty (P6SourceClosure D C1 C2 C3 X T Dq Lt mu) := by
  sorry

end LeanFormal.IUT.N8Closure.C9P6Closure
