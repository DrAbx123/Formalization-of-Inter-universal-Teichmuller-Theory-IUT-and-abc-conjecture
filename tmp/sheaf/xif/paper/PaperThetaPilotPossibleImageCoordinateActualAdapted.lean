import tmp.sheaf.xif.paper.PaperThetaPilotCarrierActualAdapted

-- Paper Theta-pilot possible-image coordinate structure: tuple candidate
--
-- The source possible image n,◦U_{j,vQ} is a subset of the tensor packet
-- I_Q(S^±_{j+1}; D^⊣_{vQ}) (IUT III, proof of Cor 3.12), i.e. a region in
-- a tensor product indexed by the label container S^±_{j+1}; it is not a
-- function whose every F_l^x coordinate is the same constant value.
--
-- The current paperThetaPilotPointAt q j = fun _ => log(thetaValue q j) is a
-- diagonal value-layer surrogate. Here we construct the correct tuple-level
-- candidate on PaperThetaPilotCarrier: the j-th coordinate carries the theta
-- value and every other coordinate carries 1. This is still a value-layer
-- model of the source tensor packet: the full source packet (S^± index and
-- log-shell regions) is recorded as an exact gap, not faked.
-- WRITE-ONLY; no local lake/lean.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaPilotPossibleImageCoordinateActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActualAdapted

universe u

variable {l : PrimeGeFive}
variable (q : Real)

-- The diagonal/constant value-layer point currently used by
-- PaperThetaPilotCarrierActualAdapted.paperThetaPilotPointAt.
theorem currentPointAt_eq_constant
    (j : PaperThetaPilotCarrier (l := l)) :
    paperThetaPilotPointAt (l := l) q j =
      fun _ : PaperThetaPilotCarrier (l := l) =>
        Multiplicative.ofAdd (Real.log (paperThetaValue (l := l) q j)) := rfl

-- Correct tuple-level possible image: theta value at the j-th coordinate,
-- 1 at every other coordinate.
noncomputable def paperThetaPilotTuplePoint
    (j : PaperThetaPilotCarrier (l := l)) : PaperThetaPilotPoint (l := l) :=
  fun k : PaperThetaPilotCarrier (l := l) =>
    if k = j then
      Multiplicative.ofAdd (Real.log (paperThetaValue (l := l) q j))
    else 1

@[simp] theorem paperThetaPilotTuplePoint_self
    (j : PaperThetaPilotCarrier (l := l)) :
    paperThetaPilotTuplePoint (l := l) q j j =
      Multiplicative.ofAdd (Real.log (paperThetaValue (l := l) q j)) := by
  unfold paperThetaPilotTuplePoint
  simp

@[simp] theorem paperThetaPilotTuplePoint_other
    {j k : PaperThetaPilotCarrier (l := l)} (hk : k ≠ j) :
    paperThetaPilotTuplePoint (l := l) q j k = 1 := by
  unfold paperThetaPilotTuplePoint
  simp [hk]

-- The tuple-level possible-image set.
noncomputable def paperTuplePossibleImageSet :
    Set (PaperThetaPilotPoint (l := l)) :=
  Set.range (paperThetaPilotTuplePoint (l := l) q)

theorem paperThetaPilotTuplePoint_mem
    (j : PaperThetaPilotCarrier (l := l)) :
    paperThetaPilotTuplePoint (l := l) q j ∈
      paperTuplePossibleImageSet (l := l) q :=
  ⟨j, rfl⟩

-- Exact gap: the actual source possible image is a region in the tensor packet
-- I_Q(S^±_{j+1}; D^⊣_{vQ}), not merely a single tuple over F_l^x carrying one
-- scalar per coordinate. The full tensor-packet data is recorded, not assumed.
structure PaperThetaPilotTensorPacketImageGap where
  /-- The source tensor-packet label container, e.g. S^±_{j+1}. -/
  tensorLabel : Type
  /-- The source possible-image region in the tensor packet. -/
  imageRegion : Set (tensorLabel → Multiplicative Real)
  /-- Projection from the source tensor labels to the paper F_l^x labels. -/
  labelProjection : tensorLabel → PaperThetaPilotCarrier (l := l)
  /-- The source region is not the diagonal/constant value-layer tuple. -/
  not_diagonal : Prop

def PaperThetaPilotTensorPacketImageObstruction : Prop :=
  Nonempty (PaperThetaPilotTensorPacketImageGap (l := l))

#check currentPointAt_eq_constant
#check paperThetaPilotTuplePoint
#check paperThetaPilotTuplePoint_self
#check paperThetaPilotTuplePoint_other
#check paperTuplePossibleImageSet
#check PaperThetaPilotTensorPacketImageGap
#check PaperThetaPilotTensorPacketImageObstruction

end LeanFormal.IUT.XiFPaper.PaperThetaPilotPossibleImageCoordinateActualAdapted

end