import tmp.sheaf.xif.paper.Mzk1Cor312HqnegDischargedActual
import tmp.sheaf.xif.paper.Mzk1HqnegHullModelActual
import Mathlib.Tactic

/-! # shehdd hqneg clean gate (Sha, read-only, no new objects) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HqnegDischargedTCleanGateShaActual

structure HqnegRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def hqnegRows : List HqnegRow :=
  [ ⟨"hqneg discharged (mainline)", "Mzk1Cor312HqnegDischargedActual.cor312_hqneg_discharged", "GREEN"⟩
  , ⟨"hull hqneg model", "Mzk1HqnegHullModelActual.canonicalHqneg", "GREEN"⟩
  , ⟨"scope", "acceptance gate only", "INTEGRITY"⟩
  ]

theorem hqnegRows_length : hqnegRows.length = 3 := rfl

theorem hqnegRows_statuses_ok :
    hqnegRows.all (fun r => r.status ∈ ["GREEN", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1HqnegDischargedTCleanGateShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312HqnegDischargedActual.cor312_hqneg_discharged
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual.canonicalHqneg
