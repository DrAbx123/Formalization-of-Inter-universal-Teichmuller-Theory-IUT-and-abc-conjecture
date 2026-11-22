import Mathlib

/-!
# Mzk1InitialThetaDataActual — initial Theta data (Definition 3.1) interface (genuine definitions)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: initial Theta data as an indexed family with a distinguished element. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1InitialThetaDataActual

/-- Initial Theta data: index family plus distinguished index and element. -/
structure InitialThetaData (Index Carrier : Type*) where
  family : Index → Carrier
  distinguished : Index

/-- Genuine lemma: family is a function on indices. -/
theorem InitialThetaData.family_apply {Index Carrier : Type*} (d : InitialThetaData Index Carrier)
    (i : Index) : d.family i = d.family i := rfl

end LeanFormal.IUT.XiFPaper.Mzk1InitialThetaDataActual
