import tmp.sheaf.xif.paper.Mzk1Lemma24StatementShapeActual
import tmp.sheaf.xif.paper.Mzk1Lemma24NormalizationTransferActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Mzk1Lemma24NormalizationIntegrationActual — OPTIONAL precise statement (Lead de-prioritized).
Green evidence for the transfer layer remains Mzk1Lemma24NormalizationTransferActual.
This file records the PRECISE integration statement (no True/toy payload); it is NOT
claimed as evidence.  Registry frozen 14041. -/
namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24NormalizationIntegrationActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24StatementShapeActual
open Polynomial

/-- Precise integration statement (named, NOT proved): for any finite S and beta not
in S, and monic p of degree d with coefficient bound C, some normalization yields a
Lemma-2.4 shape for the ORIGINAL (S, beta). -/
def mzk1NormalizationIntegrationStatement : Prop :=
  ∀ (d : Nat) (hd : 1 ≤ d) (C : ℝ) (hC1 : 1 ≤ C)
    (p : Polynomial ℂ) (hmon : p.Monic) (hdeg : p.natDegree = d)
    (hcoeff : ∀ k, k < d → ‖p.coeff k‖ ≤ C)
    (S : Finset ℂ) (β : ℂ), β ∉ S →
    ∀ (unramifiedAt : P1Point ℂ → Prop),
    ∃ (targetSet : Set (P1Point ℂ)),
      Mzk1Lemma24StatementShape ℂ (S.image P1Point.ofFinite) (P1Point.ofFinite β)
        targetSet unramifiedAt

#check mzk1NormalizationIntegrationStatement

end LeanFormal.IUT.XiFPaper.Mzk1Lemma24NormalizationIntegrationActual
end