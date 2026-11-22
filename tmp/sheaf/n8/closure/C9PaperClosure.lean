import tmp.sheaf.n8.closure.C9QThetaValuesNamed
import tmp.sheaf.n8.closure.P6ChainA
import tmp.sheaf.n8.closure.P6L
import tmp.sheaf.n8.closure.P6Comparison

/-!
# C9 paper closure — Q/Theta/Values plus P6 comparison

Reuses C9QThetaValuesNamed, P6ChainA, P6L, P6Comparison.  PaperC9Output bundles:

- Q from P6ChainA (the actual native q scalar);
- Theta and Values from the exact P6L global readout source object;
- the P6 exact/epsilon comparison.

No legacy C9Native/C9Proof target and no C9Paper free-field structure is imported
or recreated.  The only named sorry is the source-object existence
paperC9Output_nonempty; the condition reductions are proved.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C9PaperClosure

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Assembled C9 paper output: Q, Theta, Values and P6 comparison. -/
structure PaperC9Output (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] where
  /-- Chain A: actual native q -> L_q -> Q. -/
  chainA : P6ChainA.P6ChainAData X
  /-- Exact Theta source object: global P6L readout. -/
  theta : ThetaSourceObject (X := X) mu
  /-- Exact Values source witness: the same global P6L readout object. -/
  valuesWitness : ValuesSourceObject (X := X) mu

namespace PaperC9Output

variable {X : N8NativeInput l}
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
variable (O : PaperC9Output X mu)

/-- Q is Chain A's Q. -/
def Q : Real := QNamed X O.chainA

/-- Theta is the exact readout value of the Theta source object. -/
def Theta : Real := ThetaNamed (X := X) (mu := mu) O.theta

/-- Values is the exact ellOut image family, not a stored Real set. -/
def valuesSet (O : PaperC9Output X mu) : Set Real := ValuesNamed (X := X) mu

/-- Q is exactly the actual native q scalar. -/
theorem Q_eq_nativeScalar : O.Q = qPilotSignedLog X :=
  QNamed_eq_nativeScalar X O.chainA

end PaperC9Output

/-- ValuesBounded is the exact condition that every actual ellOut value is at
most Theta. -/
def ValuesBounded {X : N8NativeInput l}
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    (O : PaperC9Output X mu) : Prop :=
  ∀ z : Real, z ∈ PaperC9Output.valuesSet O -> z <= O.Theta

/-- Exact reduction of ValuesBounded to the source readout objects. -/
theorem valuesBounded_iff {X : N8NativeInput l}
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    (O : PaperC9Output X mu) :
    ValuesBounded O ↔
      ∀ R : ValuesSourceObject (X := X) mu, R.ellOutValue <= O.Theta := by
  constructor
  · intro h R
    exact h R.ellOutValue ⟨R, rfl⟩
  · intro h z hz
    rcases hz with ⟨R, rfl⟩
    exact h R

/-- Q belongs to the paper R^{<= Theta} surface. -/
def QInRleqTheta {X : N8NativeInput l}
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    (O : PaperC9Output X mu) : Prop :=
  O.Q ∈ {z : Real | z <= O.Theta}

/-- Exact condition reduction for Q membership. -/
theorem qInRleqTheta_iff {X : N8NativeInput l}
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    (O : PaperC9Output X mu) :
    QInRleqTheta O ↔ O.Q <= O.Theta := Iff.rfl

/-- J type: actual source-allowed output regions. -/
abbrev PaperJType (X : N8NativeInput l) := P6Comparison.SourceAllowedOutput X

/-- J range: all source-allowed outputs; independent of Q <= Theta. -/
def PaperJRange (X : N8NativeInput l) : Set (PaperJType X) := Set.univ

/-- P6 exact/epsilon comparison as an independent theorem, not a structure
field. -/
theorem paperC9Comparison
    {X : N8NativeInput l}
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    (O : PaperC9Output X mu) :
    P6Comparison.P6Exact X O.Q ∨ P6Comparison.P6Epsilon X O.Q := by
  sorry

/-- Named source existence for the assembled paper output. -/
theorem paperC9Output_nonempty
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] :
    Nonempty (PaperC9Output X mu) := by
  sorry

end LeanFormal.IUT.N8Closure.C9PaperClosure
