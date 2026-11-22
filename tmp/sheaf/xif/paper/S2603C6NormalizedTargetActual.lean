import tmp.sheaf.xif.paper.S2602C6TargetActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper.S2602C6TargetActual
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2603C6NormalizedTargetActual

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

/-- P5 normalized target: normalized singleton log-volume at the C6 carrier. -/
def S2603P5Target
    (point : Nat -> Nat -> Nat -> S2602C6Carrier places tuple)
    (eps : Real) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    (S2602B places tuple mu).normalizedLogVolume {point a b c} <=
      (1 + eps) * arithmeticWeight (abcRationalPoint a c)

/-- P4 normalized target, paper direction: normalized region volume dominates
the weighted height. -/
def S2603P4Target
    (region : Nat -> Nat -> Nat -> Set (S2602C6Carrier places tuple))
    (eps : Real) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    (1 + eps) * arithmeticWeight (abcRationalPoint a c) <=
      (S2602B places tuple mu).normalizedLogVolume (region a b c)

/-- The unit-region/scaling data required to speak about `lambda * O` at the
C6 normalized-log-volume level (paper Remark 3.9.5). -/
structure S2603UnitScaleData where
  unitRegion : Set (S2602C6Carrier places tuple)
  scaleShift : S2602C6Carrier places tuple -> S2602C6Carrier places tuple
  hull_subset_scaleShift :
    (S2602B places tuple mu).hull <= scaleShift '' unitRegion
  unitRegion_normalized_nonpos :
    (S2602B places tuple mu).normalizedLogVolume unitRegion <= 0
  scaleShift_unitRegion_le :
    (S2602B places tuple mu).normalizedLogVolume (scaleShift '' unitRegion) <=
      (S2602B places tuple mu).normalizedLogVolume unitRegion

def S2603P5C6NormalizedTarget
    (point : Nat -> Nat -> Nat -> S2602C6Carrier places tuple)
    (eps : Real) : Prop :=
  S2603P5Target places tuple mu point eps

def S2603P4C6NormalizedTarget
    (region : Nat -> Nat -> Nat -> Set (S2602C6Carrier places tuple))
    (eps : Real) : Prop :=
  S2603P4Target places tuple mu region eps

#check S2603P5Target
#check S2603P4Target
#check S2603P5C6NormalizedTarget
#check S2603P4C6NormalizedTarget
#check S2603UnitScaleData

end LeanFormal.IUT.XiFPaper.S2603C6NormalizedTargetActual
end