import tmp.sheaf.xif.paper.S2587LocalizedResidueDataActual
noncomputable section
set_option autoImplicit false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2596kCard613Actual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual
lemma card_S_quot_WP (W : S2584PrimeDegreeOneWitness) :
    Nat.card (S2565ConcreteIntegralClosureCActual.S ⧸ W.P) = 613 := by
  calc Nat.card (S2565ConcreteIntegralClosureCActual.S ⧸ W.P)
      = Nat.card (ZMod 613) := Nat.card_congr W.residueEquivS.toEquiv
    _ = 613 := by simp [ZMod.card]
lemma card_S_quot_D (W : S2584PrimeDegreeOneWitness)
    (hirr : S2587FbarIrreducibleRequired W) :
    Nat.card (S2565ConcreteIntegralClosureCActual.S ⧸ (S2587ResidueDataOfWitness W hirr).p) = 613 :=
  card_S_quot_WP W
#print axioms card_S_quot_WP
#print axioms card_S_quot_D
end LeanFormal.IUT.XiFPaper.S2596kCard613Actual
end
