import Mathlib

/-!
# Mzk1EquivComposeChainConsumerActual — chained equivalence-composition consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumers: composition of equivalences is an equivalence with genuine inverse laws. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1EquivComposeChainConsumerActual

/-- Chained: the composed equivalence is inverse to its inverse (left law). -/
theorem trans_symm_apply_chain {S T U : Type*} (e1 : S ≃ T) (e2 : T ≃ U) (x : S) :
    (e1.trans e2).symm ((e1.trans e2) x) = x :=
  Equiv.symm_apply_apply (e1.trans e2) x

/-- Chained: the composed equivalence is inverse to its inverse (right law). -/
theorem trans_apply_symm_chain {S T U : Type*} (e1 : S ≃ T) (e2 : T ≃ U) (y : U) :
    (e1.trans e2) ((e1.trans e2).symm y) = y :=
  Equiv.apply_symm_apply (e1.trans e2) y

/-- Chained: a single equivalence satisfies both inverse laws. -/
theorem symm_comp_apply_chain {S T : Type*} (e : S ≃ T) (x : S) :
    e.symm (e x) = x :=
  e.symm_apply_apply x

end LeanFormal.IUT.XiFPaper.Mzk1EquivComposeChainConsumerActual
