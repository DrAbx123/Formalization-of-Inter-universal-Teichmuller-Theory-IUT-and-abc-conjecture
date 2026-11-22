import Mathlib.Tactic

/-!
# shehdd A632 gap structural/shape audit (Sha)

Machine-readable structural audit of the two IUT IV Thm 1.10 gaps: quantifier
shape, dependence of D on eps, region-volume vs weight, and triple dependence.
No mathematical object is changed; checks are by `decide`.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GapStructuralShapeAuditShaActual

structure GapShapeRow where
  gap : String
  quantifierShape : String
  dependenceNote : String
  status : String
  deriving Repr, DecidableEq

def gapShapeRows : List GapShapeRow :=
  [ ⟨"Gap1 (height estimate)", "forall eps>0, forall ABC triples: height <= (1+eps)*regionVolume(a,b,c)", "no existential D; region is triple-dependent", "NAMED"⟩
  , ⟨"Gap2 (volume estimate)", "forall eps>0, exists D, forall ABC triples: regionVolume <= (1+eps)*weight + hull + D", "D may depend on eps (NO uniform D)", "NAMED"⟩
  , ⟨"Gap2 uniform variant", "exists D, forall eps>0, forall triples: ... + D", "uniform D; implies pointwise additive bound", "SUPPLEMENTARY"⟩
  , ⟨"Gap1 model substitution", "logVolume := arithmeticWeight", "MODEL-only equivalence; false for 3+125=128", "SUPPLEMENTARY_MODEL_ONLY"⟩
  , ⟨"region log-volume", "paper comparison region volume (per triple)", "NOT arithmeticWeight; tripleScale a b c needed", "GREEN_OBJECT"⟩
  , ⟨"triple-dependent scaling", "scale a b c '' (unitRegion union pt a b c)", "scaleShift=id obstruction (A618)", "GREEN_OBJECT"⟩
  ]

theorem gapShapeRows_length : gapShapeRows.length = 6 := rfl

theorem gapShapeRows_statuses_ok :
    gapShapeRows.all (fun r =>
      r.status ∈ ["NAMED", "SUPPLEMENTARY", "SUPPLEMENTARY_MODEL_ONLY", "GREEN_OBJECT"]) = true := by
  decide

theorem gapShapeRows_has_gap1 :
    gapShapeRows.any (fun r => r.gap = "Gap1 (height estimate)") = true := by
  decide

theorem gapShapeRows_has_gap2 :
    gapShapeRows.any (fun r => r.gap = "Gap2 (volume estimate)") = true := by
  decide

theorem gapShapeRows_has_model_warning :
    gapShapeRows.any (fun r => r.status = "SUPPLEMENTARY_MODEL_ONLY") = true := by
  decide

theorem gapShapeRows_has_triple_scaling :
    gapShapeRows.any (fun r => r.gap = "triple-dependent scaling") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1GapStructuralShapeAuditShaActual
