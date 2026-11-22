import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2590P4SourceDictionaryActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)

/-- The corrected P4 dictionary, at the source value carrier: the arithmetic
weight of x = a/c is bounded by the actual source local log-degree of the
point attached to (a,b,c).  This replaces the fixed-unit Haar region-volume
form, which is unsatisfiable because the region volume is bounded by the unit
region while arithmeticWeight is unbounded. -/
def P4SourceLogDegreeDictionary
    (p : Nat -> Nat -> Nat -> I.ThetaPilotPoint v) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    arithmeticWeight (abcRationalPoint a c) <=
      I.sourceLocalLogDegree v (p a b c)

/-- The scaled source-log-degree dictionary, the exact input consumed by
`cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary`. -/
def P4ScaledSourceLogDegreeDictionary
    (p : Nat -> Nat -> Nat -> I.ThetaPilotPoint v) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    arithmeticWeight (abcRationalPoint a c) <=
      I.sourceLocalLogDegree v (D.scaling * p a b c)

/-- Scaled P4 dictionary implies the direct source dictionary when the scaling
has nonpositive log-degree. -/
theorem P4SourceLogDegreeDictionary_of_scaled
    (p : Nat -> Nat -> Nat -> I.ThetaPilotPoint v)
    (hscaling : I.sourceLocalLogDegree v D.scaling <= 0)
    (h : P4ScaledSourceLogDegreeDictionary I v R n D p) :
    P4SourceLogDegreeDictionary I v p := by
  intro a b c habc
  have hh := h a b c habc
  have hmul := I.sourceLocalLogDegree_mul v D.scaling (p a b c)
  rw [hmul] at hh
  linarith [hscaling, hh]

/-- **P4 corrected actual reduction**: the scaled source log-degree dictionary
gives the exact \`hweightvol\` input at the actual value-realized carrier
\`sourceUnitRegionHaarInterface\`; no fixed-unit Haar region volume is assumed. -/
theorem P4_hweightvol_of_scaledDictionary
    (p : Nat -> Nat -> Nat -> I.ThetaPilotPoint v)
    (h : P4ScaledSourceLogDegreeDictionary I v R n D p) :
    forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        ((I.sourceUnitRegionHaarInterface v R n D).logVolume
          (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D)
            p a b c)).toReal :=
  I.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary
    v R n D p h

/-- Corrected P4 direct-dictionary form: the direct dictionary plus a
nonpositive scaling gives the same \`hweightvol\` input. -/
theorem P4_hweightvol_of_sourceDictionary
    (p : Nat -> Nat -> Nat -> I.ThetaPilotPoint v)
    (hscaling : I.sourceLocalLogDegree v D.scaling <= 0)
    (h : P4ScaledSourceLogDegreeDictionary I v R n D p) :
    forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        ((I.sourceUnitRegionHaarInterface v R n D).logVolume
          (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D)
            p a b c)).toReal :=
  P4_hweightvol_of_scaledDictionary I v R n D p h

#print axioms P4SourceLogDegreeDictionary_of_scaled
#print axioms P4_hweightvol_of_scaledDictionary
#print axioms P4_hweightvol_of_sourceDictionary

end LeanFormal.IUT.XiFPaper.S2590P4SourceDictionaryActual
end
