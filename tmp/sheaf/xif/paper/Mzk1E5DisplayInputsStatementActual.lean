import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual

/-!
  Mainline: structural decomposition of the IUT IV Theorem 1.10 display inputs
  (hCor312 + hSlack) and its consumer.  Statement-level only; the two hypotheses
  remain the named paper inputs.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1E5DisplayInputsStatementActual

open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

/-- hCor312: from Cor 3.12 C_Theta >= -1 (paper lines 1373-1380). -/
def Cor312GapHyp (T : Thm110DisplayTerms) : Prop :=
  thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T

/-- hSlack: paper arithmetic slack of step (v) (class B). -/
def SlackHyp (T : Thm110DisplayTerms) : Prop :=
  thm110Cor312Gap T ≤ thm110Rhs T - thm110Mid T

/-- The display inputs are exactly the two named paper hypotheses. -/
theorem displayInputs_iff (T : Thm110DisplayTerms) :
    Thm110DisplayInputs T ↔ Cor312GapHyp T ∧ SlackHyp T :=
  ⟨fun H => ⟨H.hCor312, H.hSlack⟩, fun H => ⟨H.1, H.2⟩⟩

/-- Final display from the two hypotheses (re-export). -/
theorem final_display_of_inputs (T : Thm110DisplayTerms) (H : Thm110DisplayInputs T) :
    thm110Lhs T ≤ thm110Rhs T :=
  thm110_final_display T H

end LeanFormal.IUT.XiFPaper.Mzk1E5DisplayInputsStatementActual