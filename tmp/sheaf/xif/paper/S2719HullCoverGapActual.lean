import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceArithmeticThetaPilotBridge
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual
import tmp.sheaf.n8.closure.SourcePilotRegion

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2719HullCoverGapActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui uK vι wV

/-- The exact geometric comparison missing for Stage C `hull_cover`: a map from
the arithmetic units to the source theta-pilot carrier, its degree, the theta
lifts, and the image-cover of the source holomorphic hull.  This is the same
data as `ArithmeticThetaPilotBridge`, recorded as an explicit gap rather than
assumed. -/
structure HullCoverGeometricGap
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι -> Type wV}
    (places : (i : ι) -> Va i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> Va i)
    {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  /-- Missing comparison from arithmetic units to source theta-pilot points. -/
  toSource : (ArithmeticTensorTupleBlock places tuple)ˣ →* I.ThetaPilotPoint v
  /-- Missing arithmetic degree on the unit group. -/
  degreeMap : Additive (ArithmeticTensorTupleBlock places tuple)ˣ →+ Real
  /-- Missing degree compatibility. -/
  degree_compat : ∀ a,
    I.sourceLocalLogDegree v (toSource a) = degreeMap (Additive.ofMul a)
  /-- Missing theta lift. -/
  thetaLift : SourceVolumeIndex l → (ArithmeticTensorTupleBlock places tuple)ˣ
  /-- Missing theta compatibility. -/
  theta_compat : ∀ q,
    toSource (thetaLift q) = I.sourceThetaPilotPoint v R q.1 q.2
  /-- Missing geometric hull cover. -/
  hull_cover :
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
      toSource '' {a : (ArithmeticTensorTupleBlock places tuple)ˣ |
        (a : ArithmeticTensorTupleBlock places tuple) ∈
          arithmeticTupleCanonicalHull places tuple}
  /-- Missing uniform degree bound. -/
  unit_bound : ∃ C : Real, ∀ a : (ArithmeticTensorTupleBlock places tuple)ˣ,
    (a : ArithmeticTensorTupleBlock places tuple) ∈
      arithmeticTupleCanonicalHull places tuple →
        degreeMap (Additive.ofMul a) ≤ C

/-- A geometric gap is exactly an `ArithmeticThetaPilotBridge`. -/
def geometricGapToBridge {K : Type uK} [Field K] [NumberField K]
    {p : Nat} [Fact p.Prime] {ι : Type vι} [Finite ι] {Va : ι -> Type wV}
    {places : (i : ι) -> Va i -> FinitePlaceAtPrime K p}
    {tuple : (i : ι) -> Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (G : HullCoverGeometricGap places tuple I v R n) :
    ArithmeticThetaPilotBridge places tuple I v R n where
  toSource := G.toSource
  degreeMap := G.degreeMap
  degree_compat := G.degree_compat
  thetaLift := G.thetaLift
  theta_compat := G.theta_compat
  hull_cover := G.hull_cover
  unit_bound := G.unit_bound

/-- `hull_cover` is exactly the image-cover field of the bridge: it cannot be
derived from Stage B data alone; it must be supplied together with `toSource`
and `degreeMap`. -/
theorem S2719_hullCover_of_bridge
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι -> Type wV}
    {places : (i : ι) -> Va i -> FinitePlaceAtPrime K p}
    {tuple : (i : ι) -> Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (B : ArithmeticThetaPilotBridge places tuple I v R n) :
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
      B.toSource '' {a : (ArithmeticTensorTupleBlock places tuple)ˣ |
        (a : ArithmeticTensorTupleBlock places tuple) ∈
          arithmeticTupleCanonicalHull places tuple} :=
  B.hull_cover

/-- Exact geometric no-go: under pointwise degree faithfulness, no full-hull
cover exists.  This is the actual negative calibration of
`SourceArithmeticThetaPilotBridge`. -/
theorem S2719_no_degreeFaithful_hullCover
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι -> Type wV}
    {places : (i : ι) -> Va i -> FinitePlaceAtPrime K p}
    {tuple : (i : ι) -> Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (B : ArithmeticThetaPilotBridge places tuple I v R n) :
    ¬ ((I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
        B.toSource '' {a : (ArithmeticTensorTupleBlock places tuple)ˣ |
          (a : ArithmeticTensorTupleBlock places tuple) ∈
            arithmeticTupleCanonicalHull places tuple}) :=
  no_degreeFaithful_fullHull_arithmeticThetaPilotBridge hdeg B


/-- The actual C3 tensor hull block is definitionally the arithmetic tuple
block appearing in the Stage C bridge. -/
theorem S2719_c3HullBlock_eq_tupleBlock
    {l : PrimeGeFive} {V : Type}
    {I : OriginalInput.{0, 0, 0, 0, 0} l V}
    (C3 : SourcePilotRegionData I) :
    HullBlock C3 =
      ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple := rfl

/-- Any bridge hull-cover factors through the range of `toSource`. -/
theorem S2719_hullCover_subset_range
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι -> Type wV}
    {places : (i : ι) -> Va i -> FinitePlaceAtPrime K p}
    {tuple : (i : ι) -> Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (B : ArithmeticThetaPilotBridge places tuple I v R n) :
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
      Set.range B.toSource := by
  intro x hx
  obtain ⟨a, _, rfl⟩ := B.hull_cover hx
  exact ⟨a, rfl⟩

/-- Conversely a range cover by the arithmetic hull gives `hull_cover`. -/
theorem S2719_hullCover_of_subset_image
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι -> Type wV}
    {places : (i : ι) -> Va i -> FinitePlaceAtPrime K p}
    {tuple : (i : ι) -> Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (toSource : (ArithmeticTensorTupleBlock places tuple)ˣ →* I.ThetaPilotPoint v)
    (h : (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
      toSource '' {a : (ArithmeticTensorTupleBlock places tuple)ˣ |
        (a : ArithmeticTensorTupleBlock places tuple) ∈
          arithmeticTupleCanonicalHull places tuple}) :
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
      toSource '' {a : (ArithmeticTensorTupleBlock places tuple)ˣ |
        (a : ArithmeticTensorTupleBlock places tuple) ∈
          arithmeticTupleCanonicalHull places tuple} := h

#check HullCoverGeometricGap
#check geometricGapToBridge
#check S2719_hullCover_of_bridge
#check S2719_no_degreeFaithful_hullCover
#print axioms S2719_no_degreeFaithful_hullCover

end LeanFormal.IUT.XiFPaper.S2719HullCoverGapActual
end
