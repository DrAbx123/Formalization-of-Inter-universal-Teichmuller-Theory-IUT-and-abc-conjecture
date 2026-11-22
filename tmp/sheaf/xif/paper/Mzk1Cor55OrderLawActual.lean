import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
# Mzk1Cor55OrderLawActual — derived order laws for the Cor-5.5 auxiliary ordered sets
(new theorems about Cor55Ldagger = WithBot Z from the existing Section-0 asset).
No copies/bookkeeping; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor55OrderLawActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

/-- Derived: the embedding of L into L-dagger is strictly monotone. -/
theorem cor55_embed_strictMono :
    StrictMono (fun a : Cor55L => (WithBot.some a : Cor55Ldagger)) := by
  intro a b hab
  exact WithBot.coe_lt_coe.mpr hab

/-- Derived: the embedding of L into L-dagger is injective. -/
theorem cor55_embed_injective :
    Function.Injective (fun a : Cor55L => (WithBot.some a : Cor55Ldagger)) :=
  fun a b h => WithBot.coe_inj.mp h

/-- Derived: the formal symbol is strictly below every embedded element. -/
theorem cor55_bot_lt_embed (a : Cor55L) :
    (⊥ : Cor55Ldagger) < (WithBot.some a : Cor55Ldagger) :=
  WithBot.bot_lt_coe a

/-- Derived: comparison of embedded elements is comparison in L. -/
theorem cor55_embed_lt_embed (a b : Cor55L) :
    (WithBot.some a : Cor55Ldagger) < (WithBot.some b : Cor55Ldagger) ↔ a < b :=
  WithBot.coe_lt_coe

/-- Derived: the embedding order-reflects. -/
theorem cor55_embed_le_embed (a b : Cor55L) :
    (WithBot.some a : Cor55Ldagger) ≤ (WithBot.some b : Cor55Ldagger) ↔ a ≤ b :=
  WithBot.coe_le_coe

#check cor55_embed_strictMono
#check cor55_embed_injective
#check cor55_bot_lt_embed
#check cor55_embed_lt_embed
#check cor55_embed_le_embed

end LeanFormal.IUT.XiFPaper.Mzk1Cor55OrderLawActual
end
