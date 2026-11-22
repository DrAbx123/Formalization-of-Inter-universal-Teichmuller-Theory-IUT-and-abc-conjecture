import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
  Mainline: Cor-5.5 auxiliary ordered sets L / L-dagger order laws (real proofs).
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor55OrderLawsActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

theorem cor55_L_embedding_strictMono :
    StrictMono (WithBot.some : ℤ → WithBot ℤ) :=
  fun a b h => WithBot.coe_lt_coe.mpr h

theorem cor55_some_le_some {gamma gamma' : Cor55L} :
    (WithBot.some gamma : Cor55Ldagger) ≤ WithBot.some gamma' ↔ gamma ≤ gamma' :=
  WithBot.coe_le_coe

theorem cor55_some_ne_bot (gamma : Cor55L) :
    (WithBot.some gamma : Cor55Ldagger) ≠ ⊥ := by
  simp

theorem cor55_square_le_some (gamma : Cor55L) :
    (⊥ : Cor55Ldagger) ≤ WithBot.some gamma :=
  bot_le

end LeanFormal.IUT.XiFPaper.Mzk1Cor55OrderLawsActual