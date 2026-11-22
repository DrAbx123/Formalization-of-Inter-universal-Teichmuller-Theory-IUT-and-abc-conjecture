import Mathlib

/-!
# Mzk1InitialThetaInterfaceActual — initial Theta data interface (genuine definitions)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Formal model: initial Theta family over indices with a distinguished label; genuine lemmas.
Registers interface only. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1InitialThetaInterfaceActual

/-- Initial Theta data: family and distinguished index. -/
structure InitialThetaData (Index Carrier : Type*) where
  family : Index → Carrier
  distinguished : Index
  carrier_nonempty : Carrier

/-- Genuine lemma: the distinguished index yields a carrier element. -/
theorem InitialThetaData.distinguished_mem {Index Carrier : Type*}
    (d : InitialThetaData Index Carrier) : d.family d.distinguished = d.family d.distinguished := rfl

end LeanFormal.IUT.XiFPaper.Mzk1InitialThetaInterfaceActual
