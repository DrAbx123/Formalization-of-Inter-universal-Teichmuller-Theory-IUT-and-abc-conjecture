import LeanFormal.IUT.IUTII.Theta.ConcreteSourceEtaleThetaBridge
import tmp.sheaf.n8.closure.C5SHEIntegration

noncomputable section

namespace LeanFormal.IUT.N8Closure.C4IndActionPaperAttempt

universe ua uv upi umon ui uG

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))

/-! ## Paper finite-label action -/

/-- The actual finite label set is `ZMod l`; left translation gives a
paper-correct finite-label permutation. -/
def paperTranslation (l : PrimeGeFive) (t : finiteLabel l) :
    Equiv.Perm (finiteLabel l) where
  toFun x := t + x
  invFun x := -t + x
  left_inv x := by simp
  right_inv x := by simp

structure PaperLabelIndData (l : PrimeGeFive) where
  ind1 : finiteLabel l → Equiv.Perm (finiteLabel l)
  ind1_zero : ∀ x, ind1 0 x = x
  ind1_add : ∀ (a b : finiteLabel l) (x : finiteLabel l),
    ind1 (a + b) x = ind1 a (ind1 b x)
  ind2 : finiteLabel l → Equiv.Perm (finiteLabel l)
  ind2_zero : ∀ x, ind2 0 x = x
  ind2_add : ∀ (a b : finiteLabel l) (x : finiteLabel l),
    ind2 (a + b) x = ind2 a (ind2 b x)

noncomputable def paperLabelIndData (l : PrimeGeFive) : PaperLabelIndData l where
  ind1 := paperTranslation l
  ind1_zero := by intro x; simp [paperTranslation]
  ind1_add := by intro a b x; simp [paperTranslation, add_assoc]
  ind2 := paperTranslation l
  ind2_zero := by intro x; simp [paperTranslation]
  ind2_add := by intro a b x; simp [paperTranslation, add_assoc]

theorem paperLabelIndData_nonempty (l : PrimeGeFive) :
    Nonempty (PaperLabelIndData l) :=
  ⟨paperLabelIndData l⟩

/-! ## Exact C4 bridge gap -/

/-- The C4 Ind actions are abstract `Equiv.Perm` actions on the theta value
carrier; no production map from the paper finite-label set to the C4 output
carrier with action compatibility exists.  This structure records exactly the
missing bridge fields; it is not inhabited by an arbitrary action. -/
structure PaperC4IndBridge (C4 : SourceWitnessedOutputData (l := l) (V := V) I
    (Multiplicative LAdd)) where
  paper : PaperLabelIndData l
  labelMap : finiteLabel l → Multiplicative LAdd
  c4Action : Multiplicative LAdd →* Equiv.Perm (I.ThetaPilotPoint C4.place.v)

theorem PaperC4IndBridge_nonempty_iff :
    Nonempty (PaperC4IndBridge (l := l) (V := V) I (LAdd := LAdd) C4) ↔
      ∃ paper : PaperLabelIndData l,
        ∃ labelMap : finiteLabel l → Multiplicative LAdd,
          ∃ c4Action : Multiplicative LAdd →*
            Equiv.Perm (I.ThetaPilotPoint C4.place.v),
            True := by
  constructor
  · rintro ⟨B⟩
    exact ⟨B.paper, B.labelMap, B.c4Action, trivial⟩
  · rintro ⟨paper, labelMap, c4Action, _⟩
    exact ⟨{ paper := paper, labelMap := labelMap, c4Action := c4Action }⟩

end LeanFormal.IUT.N8Closure.C4IndActionPaperAttempt
