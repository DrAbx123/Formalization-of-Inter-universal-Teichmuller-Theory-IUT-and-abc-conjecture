import LeanFormal.IUT.ABCBridge.Bridge.Cor312GapDictionaryLayer
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

namespace LeanFormal.IUT.XiFPaper.Node09DegreeUpperActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v)
variable (n : LeanFormal.IUT.Theorem311Source.OriginalInput.ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)
variable (p : Nat → Nat → Nat → I.ThetaPilotPoint v)

/-- Under degree faithfulness, some point map has point log-degree exactly the
arithmetic weight (constant theta-pilot point construction). -/
theorem exists_pointMap_degree_eq_weight
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ∃ q : Nat → Nat → Nat → I.ThetaPilotPoint v,
      ∀ a b c : Nat, IsABCTriple a b c →
        I.sourceLocalLogDegree v (D.scaling * q a b c) =
          arithmeticWeight (abcRationalPoint a c) := by
  refine ⟨fun a b c => I.constantThetaPilotPoint v R
    (Multiplicative.ofAdd
      ((arithmeticWeight (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling) /
        (Fintype.card (SourceVolumeIndex l) : Real))), ?_⟩
  intro a b c habc
  rw [I.sourceLocalLogDegree_mul v D.scaling _,
    I.sourceLocalLogDegree_constant v R _ hdeg]
  have hmul : (Fintype.card (SourceVolumeIndex l) : Real) *
      ((arithmeticWeight (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling) /
        (Fintype.card (SourceVolumeIndex l) : Real)) =
      arithmeticWeight (abcRationalPoint a c) - I.sourceLocalLogDegree v D.scaling :=
    mul_div_cancel₀ _ (cor312GapDict_sourceVolumeIndex_card_ne_zero l)
  rw [hmul]
  ring

/-- Consequently the untruncated degree upper bound is satisfiable under degree
faithfulness with D1 = 0 (for the constant theta-pilot point map). -/
theorem exists_pointMap_degree_le_weight
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    {eps : Real} (heps : 0 ≤ eps) :
    ∃ q : Nat → Nat → Nat → I.ThetaPilotPoint v,
      ∀ a b c : Nat, IsABCTriple a b c →
        I.sourceLocalLogDegree v (D.scaling * q a b c) ≤
          (1 + eps) * arithmeticWeight (abcRationalPoint a c) + 0 := by
  obtain ⟨q, hq⟩ := exists_pointMap_degree_eq_weight I v R n D hdeg
  refine ⟨q, fun a b c habc => ?_⟩
  rw [hq a b c habc]
  have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) := arithmeticWeight_nonneg _
  nlinarith

/-- Exact residual: satisfiability of the degree bound is not the application's
actual point map; P7 product volume still has to supply the application bound. -/
def Node09DegreeUpperResidual : List String :=
  [ "RETRACTED AS EVIDENCE: exists_pointMap_degree_eq_weight assumes D+hdeg; hull proves D and hdeg are jointly inconsistent (sourceHullVolume_eq_top_of_degreeFaithful vs finiteness), so the theorem is vacuous and is not evidence for the actual point map",
    "vacuous for the same reason; the paper-level input is the degree upper bound sourceLocalLogDegree v (scaleShift point) <= (1+eps)*arithmeticWeight + D1 for the actual point, and it must come from source data not from this file",
    "P7 report section 9.1/9.2 gives the q-ideal product-region volume V(J_q;C_q) = -sum n f log p (weighted M_q), but no singleton point-volume donor; comparing the singleton to the product region remains the paper-level IUT IV estimate",
    "no inhabitant of the cards family is constructed; this file is excluded from the cards main chain because its hdeg+D premise pair is inconsistent under the hull obstruction" ]

end LeanFormal.IUT.XiFPaper.Node09DegreeUpperActual
