import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind2Reduction

/-!
# ShehddInd2LinkChainActual — (Ind2) alien-link descent chain

Reuses the compiled uncovered tree asset Ind2Reduction (one of the ACTUAL-TARGETS
iut-skeleton:Ind2 prerequisites) as genuine chain theorems: the second link transports both
indeterminacy step forms, descends to the joint indeterminacy quotient, and the descent is
the unique lift; on the diagonal copy it is the identity; level preservation prevents
class collapse.

No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddInd2LinkChainActual

open LeanFormal.IUT
open LeanFormal.IUT.MultiradialKernel

universe u v

variable {LabelNative LabelAlien : Type u} {Native Alien : Type v}
  [AddGroup LabelNative] [AddGroup LabelAlien]

/-- **PROVED chain:** the alien second link transports (Ind1) and (Ind2) steps, its
descent is the unique quotient map with the prescribed values on representatives, and it
equals the generic quotient-compatible lift. -/
theorem ind2_alien_link_chain
    (D : Ind2AlienLink LabelNative LabelAlien Native Alien) :
    (∀ a : Native, D.secondLinkDescent (Quotient.mk'' a) = Quotient.mk'' (D.linkMap a)) ∧
      D.secondLinkDescent = D.asQuotientCompatibleMap.lift ∧
        (∀ {a b : Native}, Core.Ind1Step D.nativeCore a b →
          Core.Ind1Step D.alienCore (D.linkMap a) (D.linkMap b)) ∧
          (∀ {a b : Native}, Core.Ind2Step D.nativeCore a b →
            Core.Ind2Step D.alienCore (D.linkMap a) (D.linkMap b)) :=
  ⟨D.secondLinkDescent_mk, D.secondLinkDescent_eq_lift,
    fun h => D.linkMap_ind1Step h, fun h => D.linkMap_ind2Step h⟩

/-- **PROVED chain:** the descent is forced, and level preservation rules out collapsing
distinct levels (IUT III, Remark 3.11.3, (vii) at the reduction layer). -/
theorem ind2_descent_forcing_chain
    (D : Ind2AlienLink LabelNative LabelAlien Native Alien)
    (h : Core.GeneratedQuotient D.nativeCore → Core.GeneratedQuotient D.alienCore)
    (hmk : ∀ a : Native, h (Quotient.mk'' a) = Quotient.mk'' (D.linkMap a))
    (hlinkLevel : ∀ a : Native,
      D.alienCore.level (D.linkMap a) = D.nativeCore.level a)
    {a b : Native} (hlevel : D.nativeCore.level a ≠ D.nativeCore.level b) :
    h = D.secondLinkDescent ∧
      D.secondLinkDescent (Quotient.mk'' a) ≠ D.secondLinkDescent (Quotient.mk'' b) :=
  ⟨D.secondLinkDescent_unique h hmk,
    D.secondLinkDescent_no_level_collapse hlinkLevel hlevel⟩

/-- **PROVED chain:** on the diagonal (same-copy) datum, the second link changes no
indeterminacy class. -/
theorem ind2_diagonal_chain {Label : Type u} {Choice : Type v} [AddGroup Label]
    (core : Core Label Choice) :
    (Ind2AlienLink.diagonal core).secondLinkDescent = id :=
  Ind2AlienLink.diagonal_secondLinkDescent_eq_id core

end LeanFormal.IUT.XiFPaper.ShehddInd2LinkChainActual
end
