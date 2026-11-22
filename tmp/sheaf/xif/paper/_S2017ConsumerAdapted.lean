import tmp.sheaf.xif.paper.S2017VerlagerungActual

noncomputable section
open scoped DirectSum
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Verlagerung

namespace LeanFormal.IUT.XiFPaper.S2017Consumer

variable (p : Nat) [Fact (Nat.Prime p)]

-- The group-theoretic cyclotome and its dual are statable types.
example : Type := muQZ p
example : Type := muHatZ p

-- The remaining comparison statements are propositions, not assumptions.
example : Prop := muHatComparison p
example : Prop := muQZComparison p
example : Prop := localReciprocityMissing p

-- The cocone maps and the transfer compatibility.
example (H : Index p) : Stage p H →+ muQZ p := muQZof p H
example {H K : Index p} (h : H ≤ K) (v : Stage p K) :
    muQZof p H (toStage p h v) = muQZof p K v :=
  muQZof_transfer p h v

-- The universal property and its computation rule.
example (A : Type) [AddCommGroup A]
    (f : ∀ H : Index p, Stage p H →+ A)
    (hf : ∀ {H K : Index p} (h : H ≤ K) (v : Stage p K),
      f H (toStage p h v) = f K v)
    (H : Index p) (v : Stage p H) :
    muQZ_lift p A f hf (muQZof p H v) = f H v :=
  muQZ_lift_of p A f hf H v

-- The transfer itself is available on abelianizations.
example {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    Abelianization G →* Abelianization H := transferAb H

#print axioms muQZof_transfer
#print axioms muQZ_lift_unique
#print axioms map_subtype_comp_transferAb

end LeanFormal.IUT.XiFPaper.S2017Consumer
