import tmp.sheaf.xif.paper.S2719HullCoverGapActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceArithmeticThetaPilotBridge

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2775ThetaPilotBridgeCondActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2719HullCoverGapActual

universe ua uv upi umon ui uK vι wV

/-- Conditional theta-pilot bridge: the explicit `HullCoverGeometricGap` (S2719)
is exactly the missing bridge data; no fake bridge is introduced. -/
def S2775ThetaPilotBridge
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι -> Type wV}
    {places : (i : ι) -> Va i -> FinitePlaceAtPrime K p}
    {tuple : (i : ι) -> Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (G : HullCoverGeometricGap places tuple I v R n) :
    ArithmeticThetaPilotBridge places tuple I v R n :=
  geometricGapToBridge G

theorem S2775_sourceHullVolume_lt_top
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι -> Type wV}
    {places : (i : ι) -> Va i -> FinitePlaceAtPrime K p}
    {tuple : (i : ι) -> Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (G : HullCoverGeometricGap places tuple I v R n) :
    I.sourceHullVolume v R n < ⊤ :=
  sourceHullVolume_lt_top_of_arithmeticThetaPilotBridge
    (S2775ThetaPilotBridge G)

/-- The geometric cover remains the explicit hypothesis. -/
theorem S2775_hullCover
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι -> Type wV}
    {places : (i : ι) -> Va i -> FinitePlaceAtPrime K p}
    {tuple : (i : ι) -> Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (G : HullCoverGeometricGap places tuple I v R n) :
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
      (S2775ThetaPilotBridge G).toSource ''
        {a : (ArithmeticTensorTupleBlock places tuple)ˣ |
          (a : ArithmeticTensorTupleBlock places tuple) ∈
            arithmeticTupleCanonicalHull places tuple} :=
  (S2775ThetaPilotBridge G).hull_cover

#check S2775ThetaPilotBridge
#check S2775_sourceHullVolume_lt_top
#check S2775_hullCover
#print axioms S2775_sourceHullVolume_lt_top

end LeanFormal.IUT.XiFPaper.S2775ThetaPilotBridgeCondActual
end
