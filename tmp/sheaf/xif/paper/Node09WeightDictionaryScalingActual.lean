import LeanFormal.IUT.ABCBridge.Bridge.Cor312GapDictionaryLayer
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

namespace LeanFormal.IUT.XiFPaper.Node09WeightDictionaryScalingActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v)
variable (n : LeanFormal.IUT.Theorem311Source.OriginalInput.ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)
variable (p : Nat → Nat → Nat → I.ThetaPilotPoint v)

/-- Actual point map: the weight dictionary is exactly the scaling-separated
degree inequality. -/
theorem hweightDictionary_iff_scalingSeparatedForActualP :
    (∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v (D.scaling * p a b c)) ↔
    (∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v D.scaling +
          I.sourceLocalLogDegree v (p a b c)) := by
  constructor
  · intro h a b c habc
    exact (I.cor312GapDict_weightDictionary_iff_scalingSeparated
      v D.scaling (p a b c) a c).mp (h a b c habc)
  · intro h a b c habc
    exact (I.cor312GapDict_weightDictionary_iff_scalingSeparated
      v D.scaling (p a b c) a c).mpr (h a b c habc)

/-- With nonpositive scaling log-degree, the weight dictionary implies the
scaling-free degree domination for the actual point. -/
theorem hweightDictionary_implies_scalingFreeForActualP
    (hlam : I.sourceLocalLogDegree v D.scaling ≤ 0)
    (h : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v (D.scaling * p a b c)) :
    ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤ I.sourceLocalLogDegree v (p a b c) := by
  intro a b c habc
  exact (I.cor312GapDict_weightDictionary_implies_scalingFree
    v D.scaling (p a b c) hlam (h a b c habc))

/-- Exact residual: no universal actual-p weight dictionary; only
degree-faithfulness satisfiability and the scaling-separated form are available. -/
def Node09WeightDictionaryScalingResidual : List String :=
  [ "for the actual point map p the weight dictionary is equivalent to the scaling-separated inequality arithmeticWeight <= sourceLocalLogDegree v D.scaling + sourceLocalLogDegree v (p a b c)",
    "with scaling logDegree <= 0 it implies the scaling-free form arithmeticWeight <= sourceLocalLogDegree v (p a b c)",
    "no genuine status theorem for the application's actual p: cor312GapDict_weightDictionary_not_universal and cor312GapDict_exists_pointMap_weightDictionary both assume D+hdeg and are vacuous under the hull obstruction. Only the scaling-separated iff and the implies_scalingFree direction are genuine; the actual-p dictionary is neither proved nor refuted",
    "frozen gap2 from localEstimate definitions: Mzk1GapCorrespondenceAuditQpilotActual.gap2_iff_bridge identifies regionVolume_le_normalizedWeight with the localEstimate_le_weight field; no producer exists, so it remains the paper-level input",
    "no inhabitant and no fake" ]

end LeanFormal.IUT.XiFPaper.Node09WeightDictionaryScalingActual
