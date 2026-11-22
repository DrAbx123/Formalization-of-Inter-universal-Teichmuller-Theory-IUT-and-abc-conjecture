import tmp.sheaf.xif.paper.EtTh02DeepInputsActual
import tmp.sheaf.xif.paper.Mzk1EtThDeepInputsAnchorsActual

/-!
# Mzk1EtThDeepAnabelianInputsActualAdapted (adapted copy, A475 reuse) — the ten EtTh deep anabelian inputs as explicit named
hypotheses with their statement rows

STEP 0 prior-art: EtTh02DeepInputsActual (ten deep input statements), 
Mzk1EtThDeepInputsAnchorsActual (anchors + id linkage) -> REUSE.
This file states the deep anabelian inputs as an explicit named-hypothesis bundle and records
rows; no deep input is proved.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1EtThDeepAnabelianInputsActualAdapted

open LeanFormal.IUT.XiFPaper.EtTh02DeepInputsActual
open LeanFormal.IUT.XiFPaper.Mzk1EtThDeepInputsAnchorsActual

/-- The ten EtTh deep anabelian inputs as explicit named hypotheses (a list of statements
with their named proofs); the list itself is the paper input bundle. -/
structure EtThDeepAnabelianInputs where
  /-- the ten paper-level statements (ids). -/
  statements : List String
  /-- the ids are exactly the ten EtTh02 deep inputs. -/
  statements_eq : statements = etThDeepInputs.map (fun d => d.id)
  /-- the named proofs of the ten statements (kept as a parameter, not constructed). -/
  named : List String
  /-- the named list has one entry per statement. -/
  named_length : named.length = statements.length

/-- The anchor-id linkage is exactly the EtTh02 deep-input id list (re-export). -/
theorem etThDeepAnabelianInputs_ids :
    etThDeepInputAnchors.map (fun a => a.paperId) = etThDeepInputs.map (fun d => d.id) :=
  etThDeepInputAnchors_ids_eq

/-- Rows: (deep-input class, formal asset, status). -/
def etThDeepAnabelianInputRows : List (String × String × String) :=
  [ ("ten EtTh deep inputs (statements)", "etThDeepInputs / etThDeepInputAnchors", "STATEMENTS + ANCHORS"),
    ("id linkage", "etThDeepAnabelianInputs_ids", "PROVED (rfl)"),
    ("named input bundle", "EtThDeepAnabelianInputs (explicit named hypotheses)", "NAMED"),
    ("deep anabelian proofs (bi-Kummer, absolute anabelian)", "not constructed", "NAMED (paper input)") ]

/-- The deep-anabelian row record has four rows. -/
theorem etThDeepAnabelianInputRows_length : etThDeepAnabelianInputRows.length = 4 := rfl

#check EtThDeepAnabelianInputs
#check etThDeepAnabelianInputs_ids
#check etThDeepAnabelianInputRows_length

end LeanFormal.IUT.XiFPaper.Mzk1EtThDeepAnabelianInputsActualAdapted
end
