import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2602C6TargetActual

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {V : iota -> Type w}
variable [forall i, Fintype (V i)]
variable (places : (i : iota) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

def S2602C6Carrier : Type (max u v) := ArithmeticTensorTupleBlock places tuple

noncomputable def S2602B : C6ActualIQData places tuple mu :=
  C6ActualIQData.actual places tuple mu

/-- P5 C6-carrier target: point map directly on the C6 tensor carrier. -/
def S2602P5C6Target
    (point : Nat -> Nat -> Nat -> S2602C6Carrier places tuple)
    (eps : Real) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    ((S2602B places tuple mu).iqInterface.logVolume
      {(S2602B places tuple mu).iqInterface.scaleShift (point a b c)}).toReal <=
      (1 + eps) * arithmeticWeight (abcRationalPoint a c)

/-- P4 C6-carrier target: the point is produced on the C6 carrier through a
source-side bridge. -/
def S2602P4C6Target
    (point : Nat -> Nat -> Nat -> S2602C6Carrier places tuple)
    (eps : Real) : Prop :=
  S2602P5C6Target places tuple mu point eps

/-- The missing P4 volume bridge: source set volume transported to the C6
normalized log-volume along a carrier map. -/
def S2602P4VolumeBridge (X : Type*)
    (bridge : X -> S2602C6Carrier places tuple) (vol : Set X -> Real) : Prop :=
  forall S : Set X,
    (S2602B places tuple mu).normalizedLogVolume (bridge '' S) = vol S

/-- Region-level P6 shape without importing the sorry-bearing SourceAllowedOutput file. -/
def S2602C6RegionTarget (region : Set (S2602C6Carrier places tuple)) (Q : Real) : Prop :=
  region <= (S2602B places tuple mu).hull /\
    (S2602B places tuple mu).normalizedLogVolume region = Q

#check S2602P5C6Target
#check S2602P4C6Target
#check S2602P4VolumeBridge
#check S2602C6RegionTarget

end LeanFormal.IUT.XiFPaper.S2602C6TargetActual
end