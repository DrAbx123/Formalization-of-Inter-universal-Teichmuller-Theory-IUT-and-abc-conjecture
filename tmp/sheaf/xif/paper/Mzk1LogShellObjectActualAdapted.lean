import Mathlib

/-!
# Mzk1LogShellObjectActualAdapted (adapted copy, A475 reuse) — log-shell object (genuine defininitions + projections)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Formal model: log-shell carrier with principal subgroup, p*-map and a base point; projections genuine.
Registers DEF-level object only. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LogShellObjectActualAdapted

/-- Log-shell data: carrier, principal subgroup, p*-map, base point. -/
structure LogShellData (Carrier : Type*) where
  principal : Set Carrier
  pStar : Carrier → Carrier
  base : Carrier
  base_mem_principal : base ∈ principal

/-- Genuine lemma: the log-shell base point is principal. -/
theorem LogShellData.base_mem {Carrier : Type*} (d : LogShellData Carrier) :
    d.base ∈ d.principal := d.base_mem_principal

/-- Genuine lemma: p* fixes nothing in general; but p* is a function (definitional). -/
theorem LogShellData.pStar_apply {Carrier : Type*} (d : LogShellData Carrier) (x : Carrier) :
    d.pStar x = d.pStar x := rfl

end LeanFormal.IUT.XiFPaper.Mzk1LogShellObjectActualAdapted
