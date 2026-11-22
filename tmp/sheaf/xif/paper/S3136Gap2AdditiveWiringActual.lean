import tmp.sheaf.xif.paper.S3136SourceUnitRegionInstantiationAttemptActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HunitEpsilonTransferReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312GapDictionaryLayer

/-! # Stage-4 host: gap-2 wiring with actual unit-region/split/point-fin and ADDITIVE point input

PRIOR ART (§7.9, checked first):
* Cor312ComparisonGapReduction.lean:306 gap2 reduction; :409 hsplit_of_mem_unitRegion;
  :432 hptfin_of_mem_unitRegion.
* Cor312GapDictionaryLayer.lean:372 cor312GapDict_sourcePointBound_of_additiveBound
  (approved ADDITIVE input: height <= (1+eps)*weight + A, replacing the refuted
  uniform valuation bound).
* HunitEpsilonTransferReduction.lean:118 sourceInterface hunit drop-in.
* SourceUnitRegionHaarDataActual.lean:416 sourceHaarActualData (degenerate D).

WHAT IS PROVED HERE: a fully wired conditional gap-2 theorem on the prior-art source
interface: hunit from the sourceInterface drop-in with the concrete Haar datum
(D0 = 0), hsplit from point membership (:409), hptfin from membership (:432), and
hpoint from the APPROVED ADDITIVE input (:372).  Named inputs: the additive height
bound hadd, the degree/height comparison hline, and the point membership hmem.  This
uses the degenerate datum sourceHaarActualData only for the unit-region half; no
discharge of the paper's analytic inputs is claimed.

LABEL: conditional wiring (no discharge claim). Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136Gap2AdditiveWiringActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3136SourceUnitRegionInstantiationAttemptActual

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{0} l)
variable (n : ThetaPilotCarrier l)

/-- The prior-art source interface with the concrete Haar datum. -/
noncomputable def lgpSourceInterface :
    IQHullLogVolumeInterface ((sourceHaarActualOriginalInput (l := l) S).ThetaPilotPoint ()) :=
  (sourceHaarActualOriginalInput (l := l) S).sourceUnitRegionHaarInterface ()
    (sourceHaarActualImageRealization (l := l) S) n (sourceHaarActualData (l := l) S n)

/-- The unit-region bound (hunit) with D0 = 0 for the source interface. -/
theorem lgpSourceInterface_hunit :
    (lgpSourceInterface (l := l) S n).logVolume (lgpSourceInterface (l := l) S n).unitRegion
      ≤ (lgpSourceInterface (l := l) S n).logVolume (lgpSourceInterface (l := l) S n).hull +
        ENNReal.ofReal (0 : ℝ) :=
  cor312GapSupply_sourceInterface_hunit_of_epsilon_hullBound
    (I := sourceHaarActualOriginalInput (l := l) S) () (sourceHaarActualImageRealization (l := l) S) n
    (sourceHaarActualData (l := l) S n) (D₀ := 0) (by norm_num)
    (lgpSourceHaarActualData_hunitEpsilon (l := l) S n)

/-- Conditional gap-2 theorem: hunit proved, hsplit/hptfin from membership, hpoint from the
approved additive input; the only named analytic inputs are hmem, hadd, hline. -/
theorem lgpGap2_of_additive (p : Nat → Nat → Nat →
    (sourceHaarActualOriginalInput (l := l) S).ThetaPilotPoint ())
    {eps A : ℝ} (heps : 0 ≤ eps)
    (hmem : ∀ a b c : Nat, IsABCTriple a b c →
      p a b c ∈ (lgpSourceInterface (l := l) S n).unitRegion)
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (hline : ∀ a b c : Nat, IsABCTriple a b c →
      (sourceHaarActualOriginalInput (l := l) S).sourceLocalLogDegree ()
        ((sourceHaarActualData (l := l) S n).scaling * p a b c) ≤
        Height.logHeight₁ (abcRationalPoint a c)) :
    ∃ D : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
      ((lgpSourceInterface (l := l) S n).logVolume
        (normalizedComparisonRegion (lgpSourceInterface (l := l) S n) p a b c)).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((lgpSourceInterface (l := l) S n).logVolume
            (lgpSourceInterface (l := l) S n).hull).toReal + D := by
  have hsplit := cor312Gap2_hsplit_of_mem_unitRegion
    (lgpSourceInterface (l := l) S n) p hmem
  have hptfin := cor312Gap2_hptfin_of_mem_unitRegion
    (lgpSourceInterface (l := l) S n) p hmem
  have hpoint := cor312GapDict_sourcePointBound_of_additiveBound
    (I := sourceHaarActualOriginalInput (l := l) S) () (sourceHaarActualImageRealization (l := l) S) n
    (sourceHaarActualData (l := l) S n) p heps hadd hline
  exact cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
    (lgpSourceInterface (l := l) S n) p (D₁ := A) (by norm_num)
    (lgpSourceInterface_hunit (l := l) S n) hsplit hptfin hpoint

#check lgpSourceInterface
#check lgpSourceInterface_hunit
#check lgpGap2_of_additive

end LeanFormal.IUT.XiFPaper.S3136Gap2AdditiveWiringActual
end