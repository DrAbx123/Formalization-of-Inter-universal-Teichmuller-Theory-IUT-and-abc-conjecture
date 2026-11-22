import tmp.sheaf.xif.paper.Node09SingletonWeightActual
import tmp.sheaf.xif.paper.Node09SingletonPointCardsActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Node09SingletonWeightActual
open LeanFormal.IUT.XiFPaper.Node09SingletonPointCardsActual

namespace LeanFormal.IUT.XiFPaper.Node09SourceCardsActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v)
variable (n : LeanFormal.IUT.Theorem311Source.OriginalInput.ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)
variable (p : Nat → Nat → Nat → I.ThetaPilotPoint v)

/-- Source-level singleton cards from the weight dictionary and the actual
degree upper bound.  This is the exact conditional bridge from source data to
Node09SingletonPointCards. -/
def sourceSingletonCards {eps D₀ D₁ : Real}
    (heps : 0 ≤ eps) (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) ≤ 1 + eps)
    (hunit : (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).unitRegion ≤
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).hull + ENNReal.ofReal D₀)
    (hsplit : ∀ a b c : Nat, IsABCTriple a b c →
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
          (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D) p a b c) ≤
        (I.sourceUnitRegionHaarInterface v R n D).logVolume
            ((I.sourceUnitRegionHaarInterface v R n D).scaleShift '' (I.sourceUnitRegionHaarInterface v R n D).unitRegion) +
          (I.sourceUnitRegionHaarInterface v R n D).logVolume
            {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)})
    (hptfin : ∀ a b c : Nat, IsABCTriple a b c →
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
        {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)} < ⊤)
    (hregion_fin : ∀ a b c : Nat, IsABCTriple a b c →
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D) p a b c) < ⊤)
    (hweightDictionary : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤ I.sourceLocalLogDegree v (D.scaling * p a b c))
    (hdegreeBound : ∀ a b c : Nat, IsABCTriple a b c →
      I.sourceLocalLogDegree v (D.scaling * p a b c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁) :
    Node09SingletonPointCards (I.ThetaPilotPoint v)
      (I.sourceUnitRegionHaarInterface v R n D) p eps D₀ D₁ where
  heps := heps
  hD₀ := hD₀
  hval := hval
  hunit := hunit
  hsplit := hsplit
  hptfin := hptfin
  hregion_fin := hregion_fin
  hweight_le_singleton := by
    intro a b c habc
    exact hweight_le_singleton_of_weightDictionary I v R n D p hweightDictionary a b c habc
  hsingleton_le_weight := by
    intro a b c habc
    have hH : 0 ≤ (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁ := by
      have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) := arithmeticWeight_nonneg _
      nlinarith
    exact (I.cor312GapDict_singletonVolume_toReal_le_iff v (D.scaling * p a b c) hH).mpr
      (hdegreeBound a b c habc)

/-- Exact paper-level input for the source singleton cards. -/
def Node09SourceCardsResidual : List String :=
  [ "hweightDictionary: arithmeticWeight x <= sourceLocalLogDegree v (D.scaling * p a b c); genuine conditional input. Its degree-faithfulness satisfiability theorem assumes D+hdeg and is vacuous under the hull obstruction, and the not_universal theorem is likewise vacuous; actual-p dictionary neither proved nor refuted",
    "hdegreeBound: sourceLocalLogDegree v (D.scaling * p a b c) <= (1+eps)*arithmeticWeight x + D1; this is the actual point map degree upper bound, the paper-level IUT IV input (P7 product region comparison not formalized)",
    "hval/hunit/hsplit/hptfin/hregion_fin are reduced inputs; hsplit/hptfin have actual source-interface versions, hunit can be canonicalized, hregion_fin follows from region finiteness",
    "sourceSingletonCards produces Node09SingletonPointCards but no inhabitant of the two paper cards is constructed" ]

end LeanFormal.IUT.XiFPaper.Node09SourceCardsActual
