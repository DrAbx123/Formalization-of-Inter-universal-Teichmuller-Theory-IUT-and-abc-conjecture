import tmp.sheaf.xif.paper.S2534CoverHomMapActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2533CoverObjectMapActual
open LeanFormal.IUT.XiFPaper.S2534CoverHomMapActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual

namespace LeanFormal.IUT.XiFPaper.S2539QuotMapInjectiveInterfaceActual

theorem S2539QuotMap_injective_of_leftInverse
    {A B : CommAlgCat.FiniteEtale F}
    (L : S1728CoverMapClass
      (S2533ObjectMap B) (S2533ObjectMap A) →
      (A ⟶ B))
    (hL : ∀ f : A ⟶ B, L (S2534QuotMap f) = f) :
    Function.Injective (S2534QuotMap (A := A) (B := B)) := by
  intro f g h
  rw [← hL f, ← hL g, h]

#check S2539QuotMap_injective_of_leftInverse
#print axioms S2539QuotMap_injective_of_leftInverse
end LeanFormal.IUT.XiFPaper.S2539QuotMapInjectiveInterfaceActual
end