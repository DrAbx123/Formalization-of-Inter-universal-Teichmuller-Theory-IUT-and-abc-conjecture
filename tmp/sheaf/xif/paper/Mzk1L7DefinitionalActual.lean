import tmp.sheaf.xif.paper.Mzk1L7ProofActual
import Mathlib.Tactic

/-!
# A867 L7 at the definition level: explicit §12.1 L7 D_exact (shehdd)

§12.1 L7 (for `l` not dividing any `ord_v(q)`) gives the paper-faithful shape

  `D_exact = (1 - 1/(e_F·l))·log f + δ_l·log l + C₀`,

where `e_F` is the local ramification index, `f` the Artin conductor (elementary
prime conductor: `f = p`), `δ_l` the Θ-data correction and `C₀` the fixed
archimedean/2,3,5 contributions.

Here `DExactExplicit` is a **definition**, not a choice made to force L7; the
external content is entirely in `ThetaDataInvariants` (the identification of the
actual invariants with the explicit expression, `e_F = 1`, `f = p`, and the
nonnegativity of the remainder).  Under those fields L7 is proved by pure arithmetic.

No RETRACTED statement.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1L7DefinitionalActual

open LeanFormal.IUT.XiFPaper.Mzk1L7ProofActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open scoped BigOperators

/-- **Explicit §12.1 L7 shape** (paper normalization):
`(1 - 1/(e_F·l))·log f + δ_l·log l + C₀`. -/
def DExactExplicit (e_F f l δ_l C₀ : ℝ) : ℝ :=
  (1 - 1 / (e_F * l)) * Real.log f + δ_l * Real.log l + C₀

/-- General coefficient comparison: for `e_F ≥ 1`, `l ≥ 1`,
`1 - 1/l ≤ 1 - 1/(e_F·l)`. -/
theorem coeff_le_explicit {e_F l : ℝ} (he : 1 ≤ e_F) (hl : 1 ≤ l) :
    1 - 1 / l ≤ 1 - 1 / (e_F * l) := by
  have hl0 : (0 : ℝ) < l := by linarith
  have he0 : (0 : ℝ) < e_F := by linarith
  have hden : (0 : ℝ) < e_F * l := mul_pos he0 hl0
  have hle : 1 / (e_F * l) ≤ 1 / l := by
    apply one_div_le_one_div_of_le hl0
    nlinarith
  linarith

/-- **L7 from the explicit definition**: `f = p`, `e_F ≥ 1`, `l ≥ 1`,
`δ_l·log l + C₀ ≥ 0` ⇒ `(1 - 1/l)·log p ≤ DExactExplicit e_F f l δ_l C₀`. -/
theorem DExactLowerTarget_of_explicit_general
    (C : PrimeConductorCurve) (l e_F f δ_l C₀ : ℝ)
    (he : 1 ≤ e_F) (hl : 1 ≤ l) (hf : f = (C.p : ℝ))
    (hrem : 0 ≤ δ_l * Real.log l + C₀) :
    DExactLowerTarget C l (DExactExplicit e_F f l δ_l C₀) := by
  unfold DExactLowerTarget DExactExplicit
  have hlogp := logp_nonneg C
  have hcoef : 1 - 1 / l ≤ 1 - 1 / (e_F * l) :=
    coeff_le_explicit he hl
  have hmul : (1 - 1 / l) * Real.log (C.p : ℝ) ≤
      (1 - 1 / (e_F * l)) * Real.log (C.p : ℝ) :=
    mul_le_mul_of_nonneg_right hcoef hlogp
  rw [hf]
  linarith

/-- **L7, e_F = 1 specialization** (prime-conductor case: ρ̄ unramified at p). -/
theorem DExactLowerTarget_of_explicit
    (C : PrimeConductorCurve) (l f δ_l C₀ : ℝ)
    (hl : 1 ≤ l) (hf : f = (C.p : ℝ))
    (hrem : 0 ≤ δ_l * Real.log l + C₀) :
    DExactLowerTarget C l (DExactExplicit 1 f l δ_l C₀) := by
  exact DExactLowerTarget_of_explicit_general C l 1 f δ_l C₀ (by norm_num) hl hf hrem

/-- **External Θ-data invariants interface**: the actual invariants satisfy the
explicit §12.1 L7 expression.  These fields are the external input, not a theorem. -/
structure ThetaDataInvariants (C : PrimeConductorCurve) (l : ℝ) : Type where
  /-- the exact D_exact value. -/
  D_exact : ℝ
  e_F : ℝ
  f : ℝ
  δ_l : ℝ
  C₀ : ℝ
  /-- paper identity `D_exact = (1 - 1/(e_F l))log f + δ_l log l + C₀`. -/
  D_eq : D_exact = DExactExplicit e_F f l δ_l C₀
  /-- prime-conductor: `e_F = 1` (ρ̄ unramified at p). -/
  e_F_eq_one : e_F = 1
  /-- prime-conductor: `f = p`. -/
  f_eq_p : f = (C.p : ℝ)
  /-- `1 ≤ l`. -/
  l_ge_one : 1 ≤ l
  /-- remainder nonnegative: `δ_l log l + C₀ ≥ 0`. -/
  rem_nonneg : 0 ≤ δ_l * Real.log l + C₀

/-- **L7 closed at the definition level**: from the external invariants interface. -/
theorem L7_of_invariants (C : PrimeConductorCurve) (l : ℝ)
    (X : ThetaDataInvariants C l) :
    DExactLowerTarget C l X.D_exact := by
  rw [X.D_eq, X.e_F_eq_one]
  exact DExactLowerTarget_of_explicit C l X.f X.δ_l X.C₀ X.l_ge_one X.f_eq_p X.rem_nonneg

/-- Consumer: L7 (definition level) + Mestre–Oesterlé + Θ-data legality ⇒ SSIneq. -/
theorem ssIneqExplicit_of_invariants
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (l : ℕ) (L : ThetaDataLegality C l) (X : ThetaDataInvariants C (l : ℝ)) :
    SSIneqExplicit (sL (l : ℝ))
      ((C.e : ℝ) * Real.log (C.p : ℝ)) (l : ℝ)
      ((((l : ℝ) + 5) / 4) * X.D_exact) := by
  have hD : DExactLowerTarget C (l : ℝ) X.D_exact := L7_of_invariants C (l : ℝ) X
  exact ssIneqExplicit_of_dExactLower hMO C l L X.D_exact hD (logp_nonneg C)

structure L7DefRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def l7DefRows : List L7DefRow :=
  [ ⟨"DExactExplicit", "(1 - 1/(e_F l))log f + δ_l log l + C0", "DEF (paper-faithful)"⟩
  , ⟨"coeff comparison", "e_F>=1, l>=1 => 1-1/l <= 1-1/(e_F l)", "PROVED"⟩
  , ⟨"L7 general explicit", "f=p, e_F>=1, l>=1, remainder>=0 => target", "PROVED"⟩
  , ⟨"L7 e_F=1", "prime-conductor specialization", "PROVED"⟩
  , ⟨"ThetaDataInvariants", "D_eq, e_F=1, f=p, l>=1, rem>=0 external fields", "EXTERNAL_INTERFACE"⟩
  , ⟨"L7_of_invariants", "definition-level closure of L7", "PROVED"⟩
  , ⟨"ssIneqExplicit_of_invariants", "L7 + Mestre-Oesterle + legality => SSIneqExplicit", "PROVED"⟩
  , ⟨"remaining", "identify actual Θ-data invariants with the explicit fields", "PENDING (external/source)"⟩
  , ⟨"scope", "no fake D_exact; no sorry/axiom; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem l7DefRows_length : l7DefRows.length = 9 := rfl

theorem l7DefRows_has_external :
    l7DefRows.any (fun r => r.status = "EXTERNAL_INTERFACE") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1L7DefinitionalActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1L7DefinitionalActual.DExactLowerTarget_of_explicit
#print axioms LeanFormal.IUT.XiFPaper.Mzk1L7DefinitionalActual.L7_of_invariants
#print axioms LeanFormal.IUT.XiFPaper.Mzk1L7DefinitionalActual.ssIneqExplicit_of_invariants
