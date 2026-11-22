import tmp.sheaf.xif.paper.Node09S3135CardUActual
import tmp.sheaf.xif.paper.Node09Gap2ToCardsActual

noncomputable section
open scoped BigOperators ENNReal
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F5ActualReductionActual
open LeanFormal.IUT.XiFPaper.Node09S3135CardUActual

namespace LeanFormal.IUT.XiFPaper.Node09S3135ResidualMapActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)
variable (p : ℕ → ℕ → ℕ → I.ThetaPilotPoint v)

/-- The Node09 hpoint family on the source carrier, in source-set-volume form. -/
def Node09HpointFamily : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ D1 : ℝ, ∀ a b c : ℕ, IsABCTriple a b c →
    (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D1

/-- Card P is exactly the Node09 hpoint family (source-set-volume form). -/
theorem s3135_pointWeightCard_iff_node09HpointFamily :
    S3135ActualPointWeightCard I v R n D p ↔ Node09HpointFamily I v R n D p := by
  unfold S3135ActualPointWeightCard Node09HpointFamily
  rfl

/-- Exact residual map: Card P, F4 cards, and their Node09 counterparts. -/
def Node09S3135ResidualMap : List String :=
  [ "S3135ActualPointWeightCard (Card P) is exactly the Node09 hpoint family on the source carrier: family over eps>0 of singleton point-volume <= (1+eps)*weight + D1; s3135_pointWeightCard_iff_node09HpointFamily proves the identification with sourceSetVolume form",
    "Node09 hpoint is also derived from the frozen gap2 region-volume field via singletonVolume_le_regionVolume + ENNReal.toReal_mono (Node09Gap2ToCardsActual.hpoint_of_comparison); so Card P, Node09 hpoint, and the second gap2 comparison are one and the same paper input",
    "Card U is discharged unconditionally (Node09S3135CardUActual); F5 at the actual carrier therefore reduces to Card P alone plus the actual hsplit/hptfin",
    "F4 cards: S3135PointLogShellFaithfulness (exact missing; full value-group faithfulness implies it, only cyclic log-q faithfulness proved) and S3135ScalingLogDegreeZero (exact missing; carrier gives scaling logDegree <= 0, and existing equivalence with the normalized-scaling family is genuine)",
    "F4 is the height-comparison frontier clause; it is logically separate from Node09 hpoint (which is the region/point-volume side). No theorem identifies them; both remain paper-level",
    "no fake and no new axiom" ]

end LeanFormal.IUT.XiFPaper.Node09S3135ResidualMapActual
