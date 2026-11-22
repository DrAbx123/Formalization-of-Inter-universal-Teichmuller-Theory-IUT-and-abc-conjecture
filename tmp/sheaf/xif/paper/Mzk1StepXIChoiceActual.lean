import tmp.sheaf.xif.paper.Mzk1StepXIFormalizationAttemptActual
import Mathlib.Tactic

/-!
# A835 Step-(xi) choice-existence: explicit κs and verdict (shehdd)

From `Mzk1StepXIFormalizationAttemptActual` the Step-(xi) gap is
`StepXIAdditionalLemma A V κs := ∃ κ ∈ κs, -A - κ ≤ V`.
Here κs is made explicit and the question whether P5 (Ind3 volume range) can
satisfy it is settled (it cannot, except tautologically).

Conventions: `A = |log q| > 0`, `V = logVol(hull(vcI))`, `s = sFactor (nC)`.
P4 (lana ThetaShift): the LGP/Θ-link shift is `κ = -(s*A)`.
P5 (lana `exists_ind3_logVol_iff`): Ind3 log-volumes are exactly `(-inf, V]`.

* `KappaSet s A := {-(s*A)}` — under P4 the shift is fixed for the actual
  Θ-link/choice; the lana choice family only changes which BPS/theater realizes it;
* `AchievableOutputVolumes κ V := {κ + t | t ≤ V}` — log-volumes of LGP outputs
  (since output = κ + logVol(S) and `logVol(S) ≤ V`);
* `choiceCondition A V κ ↔ ∃ output v ≥ -A` (Step xi: output computes q-pilot);
* under P4 this is `(s-1)A ≤ V` = SSIneq;
* P5 alone is NOT sufficient: counterexample `A=2, V=0, s=2, κ=-4` (P4 holds, P5
  range holds, condition fails).

**Verdict:** the needed inequality is exactly
`∃ t ≤ V, (s-1)A ≤ t` (i.e. `∃ S ∈ Ind3, (s-1)A ≤ logVol S ≤ V`), which by P5
exists **iff** `(s-1)A ≤ V` — the SSIneq itself.  P5's upper cap `V` is the obstruction;
no volume-range argument can close the gap.  What is needed beyond P1–P5 is a choice/
alignment making the LGP output reach `-A` (lana `WallOn`/`XiPrinciple`).

No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIChoiceActual

open LeanFormal.IUT.XiFPaper.Mzk1StepXIFormalizationAttemptActual
open scoped BigOperators

/-- P5 as an abstract interface: Ind3 log-volumes fill `(-inf, V]`. -/
def Ind3VolumeRange (V : ℝ) : Prop := ∀ t : ℝ, t ≤ V → ∃ Svol : ℝ, Svol = t

/-- Under P4, the Θ-link shift set is the singleton `{-(s*A)}`. -/
def KappaSet (s A : ℝ) : Set ℝ := {-(s * A)}

theorem kappaSet_nonempty (s A : ℝ) : (KappaSet s A).Nonempty := ⟨-(s*A), rfl⟩

theorem kappaSet_eq_singleton (s A : ℝ) : KappaSet s A = {-(s*A)} := rfl

/-- Log-volumes of LGP outputs: `κ + logVol(S)` with `logVol(S) ≤ V`. -/
def AchievableOutputVolumes (κ V : ℝ) : Set ℝ :=
  {v : ℝ | ∃ t : ℝ, t ≤ V ∧ v = κ + t}

/-- The Step-(xi) choice condition: some output reaches the q-pilot lhs `-A`. -/
def ChoiceCondition (A V κ : ℝ) : Prop := -A - κ ≤ V

/-- Choice condition ⇔ some achievable output is `≥ -A`. -/
theorem choiceCondition_iff_exists_output (A V κ : ℝ) :
    ChoiceCondition A V κ ↔
      ∃ v ∈ AchievableOutputVolumes κ V, -A ≤ v := by
  unfold ChoiceCondition AchievableOutputVolumes
  constructor
  · intro h
    exact ⟨κ + V, ⟨V, le_rfl, rfl⟩, by linarith⟩
  · rintro ⟨v, ⟨t, htV, rfl⟩, hv⟩
    linarith

/-- P5 formulation: the condition is `∃ t ≤ V, (s-1)A ≤ t`. -/
theorem choiceCondition_iff_ind3_threshold (A V κ s : ℝ)
    (hP4 : κ = -(s * A)) :
    ChoiceCondition A V κ ↔ ∃ t : ℝ, t ≤ V ∧ (s - 1) * A ≤ t := by
  unfold ChoiceCondition
  rw [hP4]
  constructor
  · intro h
    exact ⟨V, le_rfl, by linarith⟩
  · rintro ⟨t, htV, ht⟩
    linarith

/-- **P4 + choice condition = SSIneq**. -/
theorem choiceCondition_iff_ssIneq (A V κ s : ℝ) (hP4 : κ = -(s * A)) :
    ChoiceCondition A V κ ↔ (s - 1) * A ≤ V := by
  unfold ChoiceCondition
  rw [hP4]
  constructor <;> intro h <;> linarith

/-- **P5 cannot close the gap**: the volume range alone does not imply the choice
condition; explicit counterexample `A=2, V=0, s=2, κ=-4`. -/
theorem P5_not_sufficient :
    ¬ (∀ (A V s κ : ℝ), κ = -(s * A) → Ind3VolumeRange V →
        ChoiceCondition A V κ) := by
  intro h
  have hrange : Ind3VolumeRange 0 := by
    intro t ht
    exact ⟨t, rfl⟩
  have hc := h 2 0 2 (-4) (by norm_num) hrange
  unfold ChoiceCondition at hc
  norm_num at hc

/-- **Exact needed inequality** (P5 form): there is an Ind3 volume `t` with
`(s-1)A ≤ t ≤ V`.  P5 supplies such `t` **iff** `(s-1)A ≤ V`; the upper cap `V` is the
obstruction, i.e. the condition is exactly SSIneq. -/
theorem needed_ind3_inequality (A V κ s : ℝ) (hP4 : κ = -(s * A)) :
    ChoiceCondition A V κ ↔ ∃ t : ℝ, t ≤ V ∧ (s - 1) * A ≤ t := by
  exact choiceCondition_iff_ind3_threshold A V κ s hP4

/-- The additional lemma with the explicit singleton `κs`: it is exactly SSIneq. -/
theorem additionalLemma_iff_ssIneq (A V s : ℝ) :
    StepXIAdditionalLemma A V (KappaSet s A) ↔ (s - 1) * A ≤ V := by
  unfold StepXIAdditionalLemma KappaSet StepXIChoiceCondition
  constructor
  · rintro ⟨κ, hκ, hcond⟩
    have hκeq : κ = -(s * A) := by simpa using hκ
    rw [hκeq] at hcond
    linarith
  · intro h
    exact ⟨-(s*A), rfl, by linarith⟩

structure ChoiceRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def choiceRows : List ChoiceRow :=
  [ ⟨"kappa set", "KappaSet s A = {-(s*A)} (P4 fixes the Θ-link shift)", "DEF"⟩
  , ⟨"achievable outputs", "{κ+t | t ≤ V}", "DEF"⟩
  , ⟨"choice condition", "-A-κ <= V <-> some output >= -A", "PROVED"⟩
  , ⟨"P4 => SSIneq", "choice condition <-> (s-1)A <= V", "PROVED"⟩
  , ⟨"P5 threshold", "<-> exists t <= V with (s-1)A <= t", "PROVED"⟩
  , ⟨"P5 unsufficient", "counterexample A=2,V=0,s=2,κ=-4", "PROVED"⟩
  , ⟨"needed extra", "choice/alignment reaching -A (lana WallOn/XiPrinciple); equivalently (s-1)A <= V", "PENDING (single Step-xi lemma)"⟩
  , ⟨"scope", "no fake closure; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem choiceRows_length : choiceRows.length = 8 := rfl

theorem choiceRows_has_pending :
    choiceRows.any (fun r => r.status = "PENDING (single Step-xi lemma)") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1StepXIChoiceActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIChoiceActual.choiceCondition_iff_exists_output
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIChoiceActual.choiceCondition_iff_ssIneq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIChoiceActual.P5_not_sufficient
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIChoiceActual.additionalLemma_iff_ssIneq
