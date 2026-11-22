import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer
import LeanFormal.IUT.ABCBridge.Bridge.Cor312GapDictionaryLayer

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

namespace LeanFormal.IUT.XiFPaper.Node09SingletonWeightActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : LeanFormal.IUT.Theorem311Source.OriginalInput.ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)
variable (p : Nat → Nat → Nat → I.ThetaPilotPoint v)

/-- Lower singleton bound from the weight dictionary: the weight is bounded by
the point log-degree, and the singleton volume is the ofReal of that degree. -/
theorem hweight_le_singleton_of_weightDictionary
    (h : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v (D.scaling * p a b c)) :
    ∀ a b c : Nat, IsABCTriple a b c →
      ENNReal.ofReal (arithmeticWeight (abcRationalPoint a c)) ≤
        I.sourceSetVolume v {D.scaling * p a b c} := by
  intro a b c habc
  rw [I.cor312GapSupply_sourceSetVolume_singleton]
  show ENNReal.ofReal (arithmeticWeight (abcRationalPoint a c)) ≤
    ENNReal.ofReal (I.sourceLocalLogDegree v (D.scaling * p a b c))
  exact ENNReal.ofReal_le_ofReal (h a b c habc)

/-- Equivalence: the upper singleton bound is exactly the untruncated degree
upper bound (no height comparison). -/
theorem hsingleton_le_weight_iff_degreeBound
    (x : I.ThetaPilotPoint v) {eps D₁ : ℝ}
    (hH : 0 ≤ (1 + eps) * arithmeticWeight (abcRationalPoint 1 2) + D₁) :
    (I.sourceSetVolume v {x}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint 1 2) + D₁ ↔
      I.sourceLocalLogDegree v x ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint 1 2) + D₁ :=
  I.cor312GapDict_singletonVolume_toReal_le_iff v x hH

/-- Exact paper-level residual for the singleton route. -/
def Node09SingletonWeightResidual : List String :=
  [ "hweight_le_singleton is proved from the weight dictionary: arithmeticWeight <= sourceLocalLogDegree gives ofReal weight <= sourceSetVolume singleton by cor312GapSupply_sourceSetVolume_singleton + ENNReal.ofReal_le_ofReal",
    "hsingleton_le_weight remains the untruncated degree upper bound sourceLocalLogDegree v (scaleShift point) <= (1+eps)*arithmeticWeight + D1 (by cor312GapDict_singletonVolume_toReal_le_iff); this is the direct point-volume/degree estimate, not a height comparison",
    "P7 report section 9.1/9.2 gives the q-ideal product-region volume V(J_q;C_q) = -sum n f log p (weighted M_q), but no singleton point-volume donor; comparing the singleton to the product region is the paper-level IUT IV estimate",
    "no inhabitant is constructed; the weight dictionary is a genuine conditional input. The degree-faithfulness satisfiability theorem cor312GapDict_exists_pointMap_weightDictionary assumes D+hdeg and is vacuous under the hull obstruction; only the scaling-separated iff/implies criteria are genuine. The actual-p dictionary is neither proved nor refuted here, and the degree upper bound remains paper-level" ]

end LeanFormal.IUT.XiFPaper.Node09SingletonWeightActual
