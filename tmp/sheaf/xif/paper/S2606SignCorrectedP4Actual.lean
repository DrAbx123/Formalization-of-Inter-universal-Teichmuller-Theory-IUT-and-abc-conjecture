import tmp.sheaf.n8.closure.SourceWitnessedOutput
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C4Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2606SignCorrectedP4Actual

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {Label : Type uL} [Group Label]
variable (D : SourceWitnessedOutputData (l := l) (V := V) I Label)
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint D.place.v)
variable (j : Nat -> Nat -> Nat -> SignedLabel l.value)

/-- The paper's positive signed log-volume: `-log Θ`, not the signed
`sourceLocalLogDegree` (which is negative when `q < 1`). -/
noncomputable def sourceSetVolumeSigned
    (S : Set (I.ThetaPilotPoint D.place.v)) : ENNReal :=
  ⨆ y ∈ S, ENNReal.ofReal (- I.sourceLocalLogDegree D.place.v y)

theorem sourceSetVolumeSigned_singleton (y : I.ThetaPilotPoint D.place.v) :
    sourceSetVolumeSigned I D {y} =
      ENNReal.ofReal (- I.sourceLocalLogDegree D.place.v y) := by
  unfold sourceSetVolumeSigned
  refine le_antisymm ?_ ?_
  · refine iSup_le fun z => iSup_le fun hz => ?_
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
  · exact le_iSup_of_le y (le_iSup_of_le (Set.mem_singleton y) le_rfl)

/-- P4 in the paper's positive sign convention. -/
def P4SignedVolumeWeightDictionary : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    arithmeticWeight (abcRationalPoint a c) <=
      (sourceSetVolumeSigned I D
        {D.eval n x (j a b c)}).toReal

theorem P4SignedVolumeWeightDictionary_iff_gauss :
    P4SignedVolumeWeightDictionary I D n x j <->
      forall a b c : Nat, IsABCTriple a b c ->
        arithmeticWeight (abcRationalPoint a c) <=
          max ((Fintype.card (SourceVolumeIndex l) : Real) *
            (((gaussExponent (j a b c).1).toNat : Real) *
              (- Real.log ((I.theaterAt 0 0).thetaPacket.q)))) 0 := by
  constructor
  · intro h a b c habc
    have hh := h a b c habc
    rw [show D.eval n x (j a b c) =
      I.sourceThetaPilotPoint D.place.v D.place.R n (j a b c) from rfl,
      sourceSetVolumeSigned_singleton,
      I.sourceLocalLogDegree_thetaPilotPoint_gauss,
      ENNReal.toReal_ofReal'] at hh
    have hneg :
        - ((Fintype.card (SourceVolumeIndex l) : Real) *
          (((gaussExponent (j a b c).1).toNat : Real) *
            Real.log ((I.theaterAt 0 0).thetaPacket.q))) =
        (Fintype.card (SourceVolumeIndex l) : Real) *
          (((gaussExponent (j a b c).1).toNat : Real) *
            (- Real.log ((I.theaterAt 0 0).thetaPacket.q))) := by ring
    rw [hneg] at hh
    exact hh
  · intro h a b c habc
    have hh := h a b c habc
    rw [show D.eval n x (j a b c) =
      I.sourceThetaPilotPoint D.place.v D.place.R n (j a b c) from rfl,
      sourceSetVolumeSigned_singleton,
      I.sourceLocalLogDegree_thetaPilotPoint_gauss,
      ENNReal.toReal_ofReal']
    have hneg :
        - ((Fintype.card (SourceVolumeIndex l) : Real) *
          (((gaussExponent (j a b c).1).toNat : Real) *
            Real.log ((I.theaterAt 0 0).thetaPacket.q))) =
        (Fintype.card (SourceVolumeIndex l) : Real) *
          (((gaussExponent (j a b c).1).toNat : Real) *
            (- Real.log ((I.theaterAt 0 0).thetaPacket.q))) := by ring
    rw [hneg]
    exact hh

/-- P5 in the paper's positive sign convention. -/
def P5SignedVolumeHeightDictionary : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    (sourceSetVolumeSigned I D {D.eval n x (j a b c)}).toReal <=
      Height.logHeight₁ (abcRationalPoint a c)

theorem P5SignedVolumeHeightDictionary_iff_gauss :
    P5SignedVolumeHeightDictionary I D n x j <->
      forall a b c : Nat, IsABCTriple a b c ->
        max ((Fintype.card (SourceVolumeIndex l) : Real) *
            (((gaussExponent (j a b c).1).toNat : Real) *
              (- Real.log ((I.theaterAt 0 0).thetaPacket.q)))) 0 <=
          Height.logHeight₁ (abcRationalPoint a c) := by
  constructor
  · intro h a b c habc
    have hh := h a b c habc
    rw [show D.eval n x (j a b c) =
      I.sourceThetaPilotPoint D.place.v D.place.R n (j a b c) from rfl,
      sourceSetVolumeSigned_singleton,
      I.sourceLocalLogDegree_thetaPilotPoint_gauss,
      ENNReal.toReal_ofReal'] at hh
    have hneg :
        - ((Fintype.card (SourceVolumeIndex l) : Real) *
          (((gaussExponent (j a b c).1).toNat : Real) *
            Real.log ((I.theaterAt 0 0).thetaPacket.q))) =
        (Fintype.card (SourceVolumeIndex l) : Real) *
          (((gaussExponent (j a b c).1).toNat : Real) *
            (- Real.log ((I.theaterAt 0 0).thetaPacket.q))) := by ring
    rw [hneg] at hh
    exact hh
  · intro h a b c habc
    have hh := h a b c habc
    rw [show D.eval n x (j a b c) =
      I.sourceThetaPilotPoint D.place.v D.place.R n (j a b c) from rfl,
      sourceSetVolumeSigned_singleton,
      I.sourceLocalLogDegree_thetaPilotPoint_gauss,
      ENNReal.toReal_ofReal']
    have hneg :
        - ((Fintype.card (SourceVolumeIndex l) : Real) *
          (((gaussExponent (j a b c).1).toNat : Real) *
            Real.log ((I.theaterAt 0 0).thetaPacket.q))) =
        (Fintype.card (SourceVolumeIndex l) : Real) *
          (((gaussExponent (j a b c).1).toNat : Real) *
            (- Real.log ((I.theaterAt 0 0).thetaPacket.q))) := by ring
    rw [hneg]
    exact hh

#print axioms P4SignedVolumeWeightDictionary_iff_gauss
#print axioms P5SignedVolumeHeightDictionary_iff_gauss

end LeanFormal.IUT.XiFPaper.S2606SignCorrectedP4Actual
end
