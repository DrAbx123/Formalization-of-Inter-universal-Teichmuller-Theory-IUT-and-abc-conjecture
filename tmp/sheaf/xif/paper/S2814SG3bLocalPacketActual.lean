import tmp.sheaf.xif.paper.S2813SG3aHullDeterminantTransportActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorIntegralRegion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2807ThetaHullVolumeIdentityActual
open LeanFormal.IUT.XiFPaper.S2813SG3aHullDeterminantTransportActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2814SG3bLocalPacketActual

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData I)

local instance s2814FiberMeasurable (i : C3.tensorIndex) :
    MeasurableSpace (CommonPrimeCompletion (c3LogShellPlace C3 i)) := borel _

local instance s2814FiberBorel (i : C3.tensorIndex) :
    BorelSpace (CommonPrimeCompletion (c3LogShellPlace C3 i)) := ⟨rfl⟩

/-- The local Haar log-volume of the actual local log-shell at a C3 tensor
index. -/
noncomputable def S2814LocalLogVolume (C3 : SourcePilotRegionData I) (i : C3.tensorIndex) : Real :=
  (haarLogVolume Measure.addHaar (actualC3LogShell C3 i)).toReal

/-- The corresponding positive local scale. -/
noncomputable def S2814LocalScale (C3 : SourcePilotRegionData I) (i : C3.tensorIndex) : Real :=
  Real.exp (S2814LocalLogVolume C3 i)

theorem S2814LocalScale_pos (C3 : SourcePilotRegionData I) (i : C3.tensorIndex) :
    0 < S2814LocalScale C3 i :=
  Real.exp_pos _

/-- The local positive packet built from the actual local log-shells. -/
noncomputable def S2814LocalPacket (C3 : SourcePilotRegionData I) : PositivePacket C3.tensorIndex where
  scale := S2814LocalScale C3
  positive := S2814LocalScale_pos C3

/-- Actual packet-log-volume computation: the packet log-volume is the sum of
the local Haar log-volumes. -/
theorem S2814_packetLogVolume_eq_sum_localLogVolume (C3 : SourcePilotRegionData I) :
    packetLogVolume (S2814LocalPacket C3) =
      ∑ i : C3.tensorIndex, S2814LocalLogVolume C3 i := by
  unfold packetLogVolume S2814LocalPacket S2814LocalScale
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.log_exp]

/-- The exact missing packet identity: the Haar log-volume of the tensor
integral region equals the sum of the local Haar log-volumes.  This is the
SG3b target; it is stated, not assumed. -/
def S2814TensorPacketIdentity (C3 : SourcePilotRegionData I) : Prop :=
  actualC3LogShellTensorLogVolume C3 =
    ∑ i : C3.tensorIndex, S2814LocalLogVolume C3 i

/-- Conditional SG3b consumer: if the missing tensor-packet identity holds,
the SG3a packet identity holds for the local packet. -/
theorem S2814_packetIdentity_of_tensorIdentity (C3 : SourcePilotRegionData I)
    (h : S2814TensorPacketIdentity C3) :
    actualC3LogShellTensorLogVolume C3 =
      packetLogVolume (S2814LocalPacket C3) := by
  rw [S2814_packetLogVolume_eq_sum_localLogVolume]
  exact h

/-- SG3b normalization factor (actual re-export): for a pure fractional
scaling datum, the normalized Haar log-volume of `(F c) * O_hol` is exactly
`-(sum_i c_i) * log p`.  This is the available exact factor formula for the
fractional-lattice model; it is not the C3 tensor-integral-region identity. -/
theorem S2818_normalizedLogVolume_fractionalLattice
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {V : iota -> Type}
    (places : (i : iota) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu]
    {c : iota -> Real}
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    arithmeticTupleNormalizedLogVolume places tuple mu
      (((arithmeticTupleFractionalLattice places tuple c *
          arithmeticTupleHolomorphicLattice places tuple :
            Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple))) =
      -((∑ i, c i) * Real.log (p : Real)) :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    places tuple mu data

#check S2814LocalLogVolume
#check S2814LocalPacket
#check S2814_packetLogVolume_eq_sum_localLogVolume
#check S2814TensorPacketIdentity
#check S2814_packetIdentity_of_tensorIdentity
#check S2818_normalizedLogVolume_fractionalLattice
#print axioms S2818_normalizedLogVolume_fractionalLattice
#print axioms S2814_packetLogVolume_eq_sum_localLogVolume
#print axioms S2814_packetIdentity_of_tensorIdentity

end LeanFormal.IUT.XiFPaper.S2814SG3bLocalPacketActual
end
