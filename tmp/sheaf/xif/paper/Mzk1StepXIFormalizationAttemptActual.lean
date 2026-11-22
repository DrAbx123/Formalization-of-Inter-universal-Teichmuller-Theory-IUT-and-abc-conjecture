import tmp.sheaf.xif.paper.Mzk1SSIneqExplicitFormActual
import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import Mathlib.Tactic

/-!
# A832 Step (xi) formalization attempt — the exact missing proposition (shehdd)

Goal: the lower-bound route `SSIneq: (sFactor-1)·|log q| <= V` from lana P1–P5.

Abstract chain (mirrors lana, no lana import — lana oleans are external):
* data: q magnitude `A = |log q|`, hull volume `V`, coefficient `s = sFactor (nC)`, and
  the LGP/Θ-link shift `κ` (log-volume shift of the output);
* P4 (transport law, lana `ThetaShift`, `MultiContainer.lean:104-107`, and
  `logVol_transport_out`, `Thm311.lean:255-262`):
  `κ = -(s * A)`;
* P5 (`Ind3` volume range, lana `exists_ind3_logVol_iff`, `Wall/Ind3.lean:252-265`):
  the `Ind3` log-volumes are exactly `(-inf, V]`; in particular every Ind3 region
  `S` has `logVol S <= V`;
* attempted derivation: if the LGP output `S'` equals the hull, then
  `V = logVol S' = -sA + logVol S`; but `logVol S <= V` makes this impossible for
  `A,s > 0` (theorem `hull_not_lgp_output_of_ind3`).  So the naive volume-range step
  cannot produce the hull as an output; a genuine choice/alignment is needed.

**The exact missing proposition (lana `WallOn`/`XiPrinciple` in volume form):**

  `StepXIAdditionalLemma (A V κset) : Prop :=
      exists κ in κset, -A - κ <= V`   (a choice with sufficient LGP shift)

Given P4 (`κ = -sA`) this is *equivalent* to SSIneq `(s-1)A <= V`
(`ssIneq_of_choiceCondition`), and P4 alone is NOT sufficient
(`P4_not_sufficient` gives an explicit counterexample).  lana proves
`WallOn <=> SSIneq` (`Thm311.lean:218 xi_iff_ss`) and `wall_iff_of_lgpLaw`
(`Wall/Checks.lean:111-120`) shows the wall is exactly the choice-existence
`exists iota, qPilot.lhs - κ_iota <= V`; `NonDerivable.lean` proves P1–P5
(`Thm311`) do not imply it.  Hence this single proposition is the Step-(xi) gap.

No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIFormalizationAttemptActual

open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual

/-- Abstract Step-(xi) volume data: q magnitude `A`, hull volume `V`, coefficient `s`,
and the LGP/Θ-link shift `κ`. -/
structure ThetaLinkVolumeData where
  /-- `A = |log q|`. -/
  A : ℝ
  /-- `V = logVol(hull(vcI))`. -/
  V : ℝ
  /-- `s = sFactor (nC)`. -/
  s : ℝ
  /-- the LGP/Θ-link log-volume shift. -/
  κ : ℝ
  /-- P4: the Θ-link transport law `logVol(LGP·S) = -s·A + logVol S`. -/
  transport : κ = -(s * A)

/-- The Step-(xi) choice condition in volume form (lana `WallOn`): there is a choice
whose LGP shift `κ` satisfies `-A - κ <= V`. -/
def StepXIChoiceCondition (A V κ : ℝ) : Prop := -A - κ ≤ V

/-- Under P4, the choice condition is SSIneq `(s-1)A <= V`. -/
theorem ssIneq_of_choiceCondition (D : ThetaLinkVolumeData)
    (h : StepXIChoiceCondition D.A D.V D.κ) :
    (D.s - 1) * D.A ≤ D.V := by
  unfold StepXIChoiceCondition at h
  have hκ : D.κ = -(D.s * D.A) := D.transport
  nlinarith

/-- **P4 alone does not give the choice condition**: explicit counterexample
`A=1, V=0, s=2, κ=-2` satisfies the transport law but `(s-1)A = 1 > 0 = V`. -/
theorem P4_not_sufficient :
    ¬ (∀ (A V s κ : ℝ), κ = -(s * A) → StepXIChoiceCondition A V κ) := by
  intro h
  have hc := h 1 0 2 (-2) (by norm_num)
  unfold StepXIChoiceCondition at hc
  norm_num at hc

/-- **The naive volume-range step is impossible**: if `V = -sA + t` and `t <= V`
(all Ind3 volumes are `<= V`), then `sA <= 0`, so for `A,s > 0` the hull cannot be
an LGP output of an Ind3 region. -/
theorem hull_not_lgp_output_of_ind3 {A s V t : ℝ}
    (hA : 0 < A) (hs : 0 < s) (ht : t ≤ V) :
    ¬ (V = -(s * A) + t) := by
  intro h
  have : 0 < s * A := mul_pos hs hA
  nlinarith

/-- **The precise additional proposition**: for the actual Θ-link/LGP choices there is
one whose shift satisfies the volume condition.  This is lana's `WallOn`/`XiPrinciple`
in volume form; it is the single Step-(xi) input beyond P1–P5. -/
def StepXIAdditionalLemma (A V : ℝ) (κs : Set ℝ) : Prop :=
  ∃ κ ∈ κs, StepXIChoiceCondition A V κ

/-- Conditional lower bound: `StepXIAdditionalLemma` for the actual shift `D.κ`
plus P4 gives SSIneq. -/
theorem ssIneq_of_additionalLemma (D : ThetaLinkVolumeData) :
    StepXIAdditionalLemma D.A D.V ({D.κ} : Set ℝ) →
      (D.s - 1) * D.A ≤ D.V := by
  intro h
  rcases h with ⟨κ, hmem, hcond⟩
  have hκ : κ = D.κ := by simpa using hmem
  subst hκ
  exact ssIneq_of_choiceCondition D hcond

/-- The additional lemma, stated directly for a choice family `κs`: it is exactly
the lana `WallOn`/`XiPrinciple` volume condition.  PENDING (lana `NonDerivable` shows
P1–P5 do not imply it). -/
structure StepXIRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def stepXIRows : List StepXIRow :=
  [ ⟨"P4 transport law", "logVol(LGP·S) = -s·A + logVol S; shift κ = -sA (lana ThetaShift/logVol_transport_out)", "GREEN (lana P4)"⟩
  , ⟨"P5 Ind3 volume range", "Ind3 log-volumes = (-inf, V] (lana exists_ind3_logVol_iff)", "GREEN (lana P5)"⟩
  , ⟨"naive hull-as-output step", "V = -sA + logVol S with logVol S <= V impossible for A,s>0", "PROVED IMPOSSIBLE"⟩
  , ⟨"StepXIChoiceCondition", "exists shift κ with -A - κ <= V", "DEF"⟩
  , ⟨"P4 alone insufficient", "explicit counterexample A=1,V=0,s=2,κ=-2", "PROVED"⟩
  , ⟨"conditional SSIneq", "choice condition + P4 => (s-1)A <= V", "PROVED"⟩
  , ⟨"StepXIAdditionalLemma", "exists κ in κs, -A - κ <= V (lana WallOn/XiPrinciple volume form)", "PENDING (the missing Step-(xi) lemma)"⟩
  , ⟨"lana evidence", "xi_iff_ss (Thm311:218), wall_iff_of_lgpLaw (Wall/Checks:111), NonDerivable: P1-P5 do not imply it", "CITED"⟩
  , ⟨"scope", "formalization attempt; no fake SSIneq; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem stepXIRows_length : stepXIRows.length = 9 := rfl

theorem stepXIRows_has_pending :
    stepXIRows.any (fun r => r.status = "PENDING (the missing Step-(xi) lemma)") = true := by
  decide
end LeanFormal.IUT.XiFPaper.Mzk1StepXIFormalizationAttemptActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIFormalizationAttemptActual.P4_not_sufficient
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIFormalizationAttemptActual.hull_not_lgp_output_of_ind3
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIFormalizationAttemptActual.ssIneq_of_choiceCondition
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIFormalizationAttemptActual.ssIneq_of_additionalLemma
