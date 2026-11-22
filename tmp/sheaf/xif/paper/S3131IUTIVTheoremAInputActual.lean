import Mathlib

/-! # S3131 IUT IV Theorem A paper-input schema (corpus: Inter-universal Teichmuller Theory IV.txt) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3131IUTIVTheoremAInputActual

universe u

/-- BD-class inequality `ht <= (1+eps)(log-diff + log-cond) + C` on a point type. -/
def BDClassInequality {X : Type u} (ht logDiff logCond : X → Real)
    (eps C : Real) : Prop :=
  ∀ x : X, ht x ≤ (1 + eps) * (logDiff x + logCond x) + C

/-- Theorem A (Diophantine Inequalities) shape: for a hyperbolic curve over a number
field, `d`, `eps > 0`, there is a constant `C` such that the BD-class inequality holds
on `U_X(Q)_{<=d}`.  (Corpus lines 93-112; [GenEll] Definition 1.2(ii), Remark 2.3.1(ii).) -/
def TheoremAStatement {X : Type u} (ht logDiff logCond : X → Real)
    (eps : Real) : Prop :=
  ∃ C : Real, BDClassInequality ht logDiff logCond eps C

/-- Theorem A yields ABC/Vojta/Szpiro as special cases (corpus lines 109-111). -/
def TheoremASpecializations (abc vo jta szpiro : Prop) : Prop :=
  abc ∧ (vo ∧ jta) ∧ szpiro

#check TheoremAStatement
#check BDClassInequality

end LeanFormal.IUT.XiFPaper.S3131IUTIVTheoremAInputActual
end