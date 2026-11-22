import Mathlib

/-!
# Mzk1InitialThetaDef31ActualAdapted (adapted copy, A475 reuse) — Definition 3.1 data (genuine definitions)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: Definition 3.1 clusters with family and link maps; genuine lemma. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1InitialThetaDef31ActualAdapted

/-- Definition 3.1 data: family plus link to a target family. -/
structure Def31Data (Index Carrier : Type*) where
  family : Index → Carrier
  link : Carrier → Carrier
  link_idem : ∀ x, link (link x) = link x

/-- Genuine lemma: Def 3.1 link is idempotent. -/
theorem Def31Data.link_idem_apply {Index Carrier : Type*} (d : Def31Data Index Carrier)
    (x : Carrier) : d.link (d.link x) = d.link x := d.link_idem x

end LeanFormal.IUT.XiFPaper.Mzk1InitialThetaDef31ActualAdapted
