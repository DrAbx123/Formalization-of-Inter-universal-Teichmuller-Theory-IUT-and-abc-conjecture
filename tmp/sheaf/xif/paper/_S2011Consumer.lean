import tmp.sheaf.xif.paper.S2011Cor110bActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual

namespace LeanFormal.IUT.XiFPaper.S2011Consumer

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The G_v-action on the actual cohomological limit is available as a monoid
homomorphism into the automorphism group. -/
example : LocalAbsoluteGalois p →* MulAut (PsiCnsCohomology p) := germAction p

/-- It acts by multiplicative automorphisms. -/
example (g : LocalAbsoluteGalois p) (x y : PsiCnsCohomology p) :
    germAction p g (x * y) = germAction p g x * germAction p g y :=
  germAction_act_mul p g x y

/-- It is an action. -/
example (g h : LocalAbsoluteGalois p) (x : PsiCnsCohomology p) :
    germAction p (g * h) x = germAction p g (germAction p h x) :=
  germAction_group_mul p g h x

/-- The translate is a multiplicative equivalence of the limit. -/
example (g : LocalAbsoluteGalois p) :
    PsiCnsCohomology p ≃* PsiCnsCohomology p := translateGermEquiv p g

/-- The weakened Frobenius normalization has the stated kernel property on the
actual Kummer image. -/
example (h : weakFrobeniusNormalization p) :
    ∃ α : PsiCnsCohomology p →* Multiplicative ℤ, Function.Surjective α ∧
      ∀ a : Otri p, α (PsiCnsKummer p a) = 1 ↔
        ∃ u : (Otri p)ˣ, (u : Otri p) = a :=
  weakFrobeniusNormalization_kernel p h

#print axioms germAction
#print axioms weakFrobeniusNormalization_kernel

end LeanFormal.IUT.XiFPaper.S2011Consumer
