import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesWitnessShaActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesEvidenceActual

/-! # ABC two-estimates components: HeightEstimate / VolumeEstimate -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesComponentsShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesWitnessShaActual

/-- The height-estimate component of the two-estimate gap. -/
def HeightEstimate (logVolume : Nat → Nat → Nat → Real) : Prop :=
  forall δ : Real, 0 < δ → forall a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c

/-- The volume-estimate component of the two-estimate gap. -/
def VolumeEstimate (logVolume : Nat → Nat → Nat → Real)
    (hullVolume : Real) : Prop :=
  forall δ : Real, 0 < δ → exists D : Real,
    forall a b c : Nat, IsABCTriple a b c →
      logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        hullVolume + D

/-- Assemble the two-estimate package from its two components. -/
noncomputable def ABCTwoEstimates.ofComponents
    (logVolume : Nat → Nat → Nat → Real) (hullVolume : Real)
    (hh : HeightEstimate logVolume) (hv : VolumeEstimate logVolume hullVolume) :
    ABCTwoEstimates where
  logVolume := logVolume
  hullVolume := hullVolume
  height_estimate := hh
  volume_estimate := hv

/-- Numeric height-estimate witness: `logVolume := logHeight` works whenever the
genuine log-height is nonnegative on ABC triples. -/
theorem heightEstimate_self_of_nonneg
    (hheight : forall a b c : Nat, IsABCTriple a b c →
      0 ≤ Height.logHeight₁ (abcRationalPoint a c)) :
    HeightEstimate (fun a b c => Height.logHeight₁ (abcRationalPoint a c)) := by
  intro δ hδ a b c htr
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hh : 0 ≤ Height.logHeight₁ (abcRationalPoint a c) := hheight a b c htr
  nlinarith [mul_nonneg hδ0 hh]

/-- Numeric volume-estimate witness: zero log-volume and zero hull volume. -/
theorem volumeEstimate_zero
    (hweight : forall (a c : Nat), 0 ≤ arithmeticWeight (abcRationalPoint a c)) :
    VolumeEstimate (fun _ _ _ => (0 : Real)) 0 := by
  intro δ hδ
  refine ⟨(0 : Real), ?_⟩
  intro a b c _
  have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) := hweight a c
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  nlinarith [mul_nonneg hδ0 hw]

/-- Components consumers: height + volume estimates give `ABCConjecture`. -/
theorem abc_of_components
    (logVolume : Nat → Nat → Nat → Real) (hullVolume : Real)
    (hh : HeightEstimate logVolume) (hv : VolumeEstimate logVolume hullVolume) :
    ABCConjecture :=
  abc_of_twoEstimates (ABCTwoEstimates.ofComponents logVolume hullVolume hh hv)

#print axioms heightEstimate_self_of_nonneg
#print axioms volumeEstimate_zero
#print axioms abc_of_components

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesComponentsShaActual
