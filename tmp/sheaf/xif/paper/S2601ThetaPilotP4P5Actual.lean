import tmp.sheaf.n8.closure.SourceWitnessedOutput
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C4Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2601ThetaPilotP4P5Actual

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {Label : Type uL} [Group Label]
variable (D : SourceWitnessedOutputData (l := l) (V := V) I Label)
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint D.place.v)
variable (j : Nat -> Nat -> Nat -> SignedLabel l.value)

/-- **Actual global theta-pilot point map**.  The point for `(a,b,c)` is the
actual C4 `eval` at a signed label `j a b c`, i.e.
`I.sourceThetaPilotPoint D.place.v D.place.R n (j a b c)`.  This replaces the
single-bad-place S2588 tensor point as the paper point map. -/
def P4ThetaPilotPointMap : Nat -> Nat -> Nat -> I.ThetaPilotPoint D.place.v :=
  fun a b c => D.eval n x (j a b c)

/-- P4 dictionary anchored to the actual global theta-pilot point. -/
def P4ThetaPilotWeightDictionary : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    arithmeticWeight (abcRationalPoint a c) <=
      I.sourceLocalLogDegree D.place.v (P4ThetaPilotPointMap I D n x j a b c)

/-- Unconditional gauss form of the P4 dictionary: the actual log-degree is
`card(SourceVolumeIndex) * ((gaussExponent j).toNat * log q)`.  No `hdeg`. -/
theorem P4ThetaPilotWeightDictionary_iff_gauss :
    P4ThetaPilotWeightDictionary I D n x j <->
      forall a b c : Nat, IsABCTriple a b c ->
        arithmeticWeight (abcRationalPoint a c) <=
          (Fintype.card (SourceVolumeIndex l) : Real) *
            (((gaussExponent (j a b c).1).toNat : Real) *
              Real.log ((I.theaterAt 0 0).thetaPacket.q)) := by
  constructor
  · intro h a b c habc
    have hh := h a b c habc
    simpa only [P4ThetaPilotPointMap, SourceWitnessedOutputData.eval,
      I.sourceLocalLogDegree_thetaPilotPoint_gauss] using hh
  · intro h a b c habc
    have hh := h a b c habc
    simpa only [P4ThetaPilotPointMap, SourceWitnessedOutputData.eval,
      I.sourceLocalLogDegree_thetaPilotPoint_gauss] using hh

/-- P5 point-height dictionary anchored to the actual global theta-pilot point. -/
def P5ThetaPilotPointHeightDictionary : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    (I.sourceSetVolume D.place.v
        {P4ThetaPilotPointMap I D n x j a b c}).toReal <=
      Height.logHeight₁ (abcRationalPoint a c)

/-- Unconditional gauss form of the P5 dictionary. -/
theorem P5ThetaPilotPointHeightDictionary_iff_gauss :
    P5ThetaPilotPointHeightDictionary I D n x j <->
      forall a b c : Nat, IsABCTriple a b c ->
        max ((Fintype.card (SourceVolumeIndex l) : Real) *
            (((gaussExponent (j a b c).1).toNat : Real) *
              Real.log ((I.theaterAt 0 0).thetaPacket.q))) 0 <=
          Height.logHeight₁ (abcRationalPoint a c) := by
  constructor
  · intro h a b c habc
    have hh := h a b c habc
    rw [I.cor312GapSupply_sourceSetVolume_singleton] at hh
    change (ENNReal.ofReal (I.sourceLocalLogDegree D.place.v
      (D.eval n x (j a b c)))).toReal <= _ at hh
    rw [show D.eval n x (j a b c) =
      I.sourceThetaPilotPoint D.place.v D.place.R n (j a b c) from rfl,
      I.sourceLocalLogDegree_thetaPilotPoint_gauss] at hh
    rw [ENNReal.toReal_ofReal'] at hh
    exact hh
  · intro h a b c habc
    have hh := h a b c habc
    rw [I.cor312GapSupply_sourceSetVolume_singleton]
    change (ENNReal.ofReal (I.sourceLocalLogDegree D.place.v
      (D.eval n x (j a b c)))).toReal <= _
    rw [show D.eval n x (j a b c) =
      I.sourceThetaPilotPoint D.place.v D.place.R n (j a b c) from rfl,
      I.sourceLocalLogDegree_thetaPilotPoint_gauss]
    rw [ENNReal.toReal_ofReal']
    exact hh

/-- **No-go for the raw theta-pilot P4 dictionary when `q <= 1`.**
If the standard q is at most one, the gauss formula gives a nonpositive
right-hand side; any ABC triple with positive arithmetic weight refutes the
dictionary.  Hence the raw source theta-pilot point cannot be the paper P4
point; the paper comparison must use a different hull/region object. -/
theorem P4ThetaPilotWeightDictionary_false_of_q_le_one
    (hq : (I.theaterAt 0 0).thetaPacket.q <= 1)
    (a b c : Nat) (habc : IsABCTriple a b c)
    (hpos : 0 < arithmeticWeight (abcRationalPoint a c)) :
    Not (P4ThetaPilotWeightDictionary I D n x j) := by
  intro hdict
  have h := hdict a b c habc
  change arithmeticWeight (abcRationalPoint a c) <=
    I.sourceLocalLogDegree D.place.v (D.eval n x (j a b c)) at h
  rw [show D.eval n x (j a b c) =
    I.sourceThetaPilotPoint D.place.v D.place.R n (j a b c) from rfl,
    I.sourceLocalLogDegree_thetaPilotPoint_gauss] at h
  have hlogq : Real.log ((I.theaterAt 0 0).thetaPacket.q) <= 0 :=
    (Real.log_nonpos_iff (I.theaterAt 0 0).thetaPacket.q_pos.le).mpr hq
  have hcard : (0 : Real) <= (Fintype.card (SourceVolumeIndex l) : Real) :=
    Nat.cast_nonneg _
  have hgauss : (0 : Real) <= ((gaussExponent (j a b c).1).toNat : Real) :=
    Nat.cast_nonneg _
  have hnonpos : (Fintype.card (SourceVolumeIndex l) : Real) *
      (((gaussExponent (j a b c).1).toNat : Real) *
        Real.log ((I.theaterAt 0 0).thetaPacket.q)) <= 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcard
      (mul_nonpos_of_nonneg_of_nonpos hgauss hlogq)
  linarith

#print axioms P4ThetaPilotWeightDictionary_iff_gauss
#print axioms P5ThetaPilotPointHeightDictionary_iff_gauss
#print axioms P4ThetaPilotWeightDictionary_false_of_q_le_one

end LeanFormal.IUT.XiFPaper.S2601ThetaPilotP4P5Actual
end
