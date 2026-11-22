import Mathlib.Tactic

/-!
# A860 E7 gap statement and the Pasten reduction (shehdd)

E7 = Shimura-curve/modular-degree route to Szpiro-6.  Literature decomposition
(fetched): Pasten, arXiv:1705.09251v4 (2018; J. Number Theory 2023) and
arXiv:2609.17390 (2026 preprint).

* `E7Scale` abstracts an elliptic curve E/ℚ: `logN`, `logDelta = log|Δ_E|`,
  `logModDegree = log δ_{D,M}` (modular degree of the optimal quotient).
* `PastenThm76 ε C`: Pasten's Thm 1.7 / Thm 7.6 —
  `log|Δ_E| < (6+ε)·log δ_{D,M} + C` (and the height analogue).
* `E7GapStatement`: the TRUE missing input — an upper bound
  `∃ C', ∀ E, log δ_{D,M} ≤ log N + C'`  (Conjecture 18.11-type).
* `E7AcceptDeltaBound := E7GapStatement`; `E7RejectDeltaBound := ¬ E7GapStatement`.

Proved here: accepting `E7GapStatement` + Pasten Thm 1.7 gives the Szpiro-6 shape
`log|Δ| ≤ 6 log N + C''` (for ε=0; general ε gives (6+ε) coefficient).
Rejecting it leaves E7 with no closure: the remaining route is to formalize the
whole Pasten 2018 chain and then still prove the same δ bound (the 2026 preprint's
`h ≪ N log log N` does not reach Szpiro-6).

Six components and their status (all external, none Lean-formalized):
RT (Thm 1.5/Cor 6.2), optimal quotient/component groups (Thm 1.4/6.17),
modular degree δ (definition; bound OPEN), Petersson norm (Thm 1.6/14.1),
Néron/Manin constant (Thm 1.3/Cor 10.2), Faltings height (Thm 1.7/7.6; 2026 Thm 1.1).

No RETRACTED statement used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1E7GapStatementActual

/-- Abstract scale of an elliptic curve on route E7. -/
structure E7Scale where
  /-- `log N_E` (conductor). -/
  logN : ℝ
  /-- `log |Δ_E|` (minimal discriminant). -/
  logDelta : ℝ
  /-- `log δ_{D,M}` (modular degree of the optimal quotient). -/
  logModDegree : ℝ

/-- Pasten 2018, Thm 1.7 / Thm 7.6: `log|Δ_E| < (6+ε)·log δ_{D,M} + C`. -/
def PastenThm76 (ε C : ℝ) (D : E7Scale) : Prop :=
  D.logDelta ≤ (6 + ε) * D.logModDegree + C

/-- The δ upper bound (Conjecture 18.11-type): `log δ_{D,M} ≤ log N + C'`. -/
def DeltaDegreeBound (C' : ℝ) : Prop :=
  ∀ D : E7Scale, D.logModDegree ≤ D.logN + C'

/-- **The true E7 gap**: an absolute upper bound for the modular degree. -/
def E7GapStatement : Prop :=
  ∃ C' : ℝ, DeltaDegreeBound C'

/-- Case 1: accept the Pasten δ bound. -/
def E7AcceptDeltaBound : Prop := E7GapStatement

/-- Case 2: do not accept it. -/
def E7RejectDeltaBound : Prop := ¬ E7GapStatement

/-- **Reduction (ε arbitrary)**: Pasten Thm 1.7 + δ bound ⇒ discriminant bound. -/
theorem szpiro_of_pasten_and_delta {ε C C' : ℝ}
    (hε : 0 ≤ 6 + ε)
    (h76 : ∀ D : E7Scale, PastenThm76 ε C D)
    (hdelta : DeltaDegreeBound C') :
    ∀ D : E7Scale,
      D.logDelta ≤ (6 + ε) * D.logN + ((6 + ε) * C' + C) := by
  intro D
  have h1 : D.logDelta ≤ (6 + ε) * D.logModDegree + C := h76 D
  have h2 : D.logModDegree ≤ D.logN + C' := hdelta D
  have hmul : (6 + ε) * D.logModDegree ≤ (6 + ε) * (D.logN + C') :=
    mul_le_mul_of_nonneg_left h2 hε
  nlinarith [h1, hmul]

/-- **Szpiro-6 shape**: with `ε = 0`, accepting the δ bound gives
`log|Δ| ≤ 6·log N + C''`. -/
theorem szpiro6_of_pasten_and_delta {C C' : ℝ}
    (h76 : ∀ D : E7Scale, PastenThm76 0 C D)
    (hdelta : DeltaDegreeBound C') :
    ∃ C'' : ℝ, ∀ D : E7Scale, D.logDelta ≤ 6 * D.logN + C'' := by
  refine ⟨6 * C' + C, ?_⟩
  intro D
  have h1 : D.logDelta ≤ 6 * D.logModDegree + C := by
    have := h76 D
    simpa [PastenThm76] using this
  have h2 : D.logModDegree ≤ D.logN + C' := hdelta D
  have hmul : 6 * D.logModDegree ≤ 6 * (D.logN + C') :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  nlinarith [h1, hmul]

/-- The case-1 reduction as a proposition: `E7AcceptDeltaBound` plus Pasten gives
a Szpiro-6 bound. -/
theorem e7_accept_reduction {C : ℝ}
    (h76 : ∀ D : E7Scale, PastenThm76 0 C D) :
    E7AcceptDeltaBound → ∃ C'', ∀ D : E7Scale, D.logDelta ≤ 6 * D.logN + C'' := by
  intro hdelta
  rcases hdelta with ⟨C', hC'⟩
  exact szpiro6_of_pasten_and_delta h76 hC'

/-- The case-2 negative control: rejecting the δ bound means the reduction above
cannot be applied.  (Pure logic: `E7RejectDeltaBound` is the negation.) -/
theorem e7_reject_no_reduction (hrej : E7RejectDeltaBound) :
    ¬ E7AcceptDeltaBound := hrej

structure E7ComponentRow where
  component : String
  pastenTheorem : String
  status : String
  deriving Repr, DecidableEq

def e7ComponentRows : List E7ComponentRow :=
  [ ⟨"RT (Ribet-Takahashi)", "Thm 1.5 / Cor 6.2: log(∏ v_p(Δ_A)) = log δ_{1,N} - log δ_{D,M} + O(log D/log log D)", "PROVED_EXTERNAL_2018 (not Lean)"⟩
  , ⟨"optimal quotient / component groups", "Thm 1.4 / Thm 6.17: uniform cokernel bound κ; Manin constant Thm 1.3 / Cor 10.2", "PROVED_EXTERNAL_2018 (not Lean)"⟩
  , ⟨"modular degree δ_{D,M}", "definition q_{D,M}∘q_{D,M}^∨ = ·δ_{D,M}; upper bound = Conj. 18.11-type", "BOUND OPEN (E7GapStatement)"⟩
  , ⟨"Petersson norm", "Thm 1.6 / Thm 14.1: -log‖f‖ ≤ (5/6+ε)log N + (1/2)log M + O(1)", "PROVED_EXTERNAL_2018 (not Lean)"⟩
  , ⟨"Néron differential / Manin constant", "Thm 1.3 / Cor 10.2: bounded Manin constant; Néron normalization", "PROVED_EXTERNAL_2018 (not Lean)"⟩
  , ⟨"Faltings height / discriminant", "Thm 1.7 / Thm 7.6: h(E)<(1/2+ε)log δ, log|Δ|<(6+ε)log δ; 2026: h≪N log log N", "PROVED_EXTERNAL_2018; 2026 PREPRINT (not peer-reviewed)"⟩
  ]

theorem e7ComponentRows_length : e7ComponentRows.length = 6 := rfl

structure E7GapRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def e7GapRows : List E7GapRow :=
  [ ⟨"E7GapStatement", "∃C, ∀E, log δ_{D,M} ≤ log N + C (modular-degree upper bound)", "DEF (the missing input)"⟩
  , ⟨"accept case", "E7GapStatement + Pasten Thm 1.7 => log|Δ| ≤ 6 log N + C'' (Szpiro-6 shape)", "PROVED (conditional reduction)"⟩
  , ⟨"reject case", "no closure; remaining: formalize Pasten 2018 chain and prove δ bound, or 2026 h≪N log log N (still not Szpiro-6)", "OPEN"⟩
  , ⟨"2026 preprint", "Thm 1.1/Cor 1.2/Cor 1.3: h≪N log log N; semistable h≪N; not Szpiro-6", "PREPRINT / NOT_FORMALIZED"⟩
  , ⟨"scope", "literature map + conditional reduction; no fake δ bound; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem e7GapRows_length : e7GapRows.length = 5 := rfl

theorem e7GapRows_has_missing :
    e7GapRows.any (fun r => r.status = "DEF (the missing input)") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1E7GapStatementActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1E7GapStatementActual.szpiro_of_pasten_and_delta
#print axioms LeanFormal.IUT.XiFPaper.Mzk1E7GapStatementActual.szpiro6_of_pasten_and_delta
#print axioms LeanFormal.IUT.XiFPaper.Mzk1E7GapStatementActual.e7_accept_reduction
