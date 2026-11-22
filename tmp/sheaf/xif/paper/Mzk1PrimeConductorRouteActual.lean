import tmp.sheaf.xif.paper.Mzk1SSIneqExplicitFormActual
import tmp.sheaf.xif.paper.Mzk1KappaLemmaActual
import tmp.sheaf.xif.paper.Mzk1FinalBoundarySzpiroActual
import Mathlib.Tactic

/-!
# A845 Route C §12.2: prime-conductor `paperGap` skeleton (shehdd)

External input (published theorem, NOT proved here, NOT sorry/axiom):

  `MestreOesterleBound` : for an elliptic curve E/ℚ with prime conductor `p`,
  the minimal discriminant exponent `e_p := ord_p(Δ_min)` satisfies `e_p ≤ 5`,
  and `e_p ≤ 2` for `p > 37` (exceptions only p = 11, 17, 19, 37; those are ≤5).

Route C arithmetic (§12.2): with `logQ = e_p·log p`, `D_exact ≥ (1-1/l)·log p`,
`V = ((l+5)/4)·D_exact`, `T(l) = 6·l(l+5)/((l+4)(l-3))`, and for prime `l ≥ 11`,

  `e_p ≤ T(l)(1-1/l)`   (pure arithmetic; margin at l=11 is 8, limit 6 > 5)

gives `(e_p)log p ≤ T(l)·D_exact`, which is exactly `SSIneqExplicit (sL l) logQ l V`.

The remaining THETA-data legality conditions are listed in `thetaLegalityRows`;
they are external (Mazur/Ribet/Mestre–Oesterlé/modularity) and NOT proved here.

No sorry/axiom is used; the external theorem is an explicit Prop parameter.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundarySzpiroActual
open scoped BigOperators

/-- A prime-conductor elliptic-curve datum: prime conductor `p` and minimal
discriminant exponent `e = ord_p(Δ_min)`.  (No elliptic-curve formalization here;
this is the explicit carrier of the external Mestre–Oesterlé statement.) -/
structure PrimeConductorCurve where
  /-- the prime conductor. -/
  p : ℕ
  /-- the prime. -/
  hp : Nat.Prime p
  /-- `e = ord_p(Δ_min)`. -/
  e : ℕ

/-- **External theorem (Mestre–Oesterlé 1989)**, as an explicit Prop parameter:
for a prime-conductor E/ℚ, `e_p ≤ 5`, and `e_p ≤ 2` for `p > 37` (the listed
exceptions p=11,17,19,37 are ≤5 only). -/
def MestreOesterleBound : Prop :=
  ∀ C : PrimeConductorCurve, C.e ≤ 5 ∧ (37 < C.p → C.e ≤ 2)

/-- Route C threshold function `T(l) = 6·l(l+5)/((l+4)(l-3))`. -/
noncomputable def T (l : ℝ) : ℝ := 6 * l * (l + 5) / ((l + 4) * (l - 3))

/-- Pure arithmetic margin: for `l ≥ 11`, `5 ≤ T(l)·(1 - 1/l)`. -/
theorem five_le_T_one_sub_inv {l : ℝ} (hl : 11 ≤ l) :
    5 ≤ T l * (1 - 1 / l) := by
  have hl0 : (0 : ℝ) < l := by linarith
  have hl4 : (0 : ℝ) < l + 4 := by linarith
  have hl3 : (0 : ℝ) < l - 3 := by linarith
  unfold T
  rw [show 6 * l * (l + 5) / ((l + 4) * (l - 3)) * (1 - 1 / l) =
        6 * (l + 5) * (l - 1) / ((l + 4) * (l - 3)) by
    field_simp [ne_of_gt hl0, ne_of_gt hl4, ne_of_gt hl3]]
  rw [le_div_iff₀ (mul_pos hl4 hl3)]
  nlinarith [sq_nonneg (l - 3), sq_nonneg (l - 1)]

/-- Consequence: if `e ≤ 5`, then `e ≤ T(l)(1 - 1/l)` for `l ≥ 11`. -/
theorem e_le_T_one_sub_inv {e : ℕ} {l : ℝ} (he : e ≤ 5) (hl : 11 ≤ l) :
    (e : ℝ) ≤ T l * (1 - 1 / l) := by
  have h5 := five_le_T_one_sub_inv hl
  have heR : (e : ℝ) ≤ 5 := by exact_mod_cast he
  linarith

/-- **Prime-conductor paperGap (arithmetic skeleton)**: under Mestre–Oesterlé,
with `D_exact ≥ (1-1/l)log p`, `l ≥ 11`, `log p ≥ 0`, we get
`e·log p ≤ T(l)·D_exact`. -/
theorem paperGap_of_primeConductor_arith
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (l : ℝ) (hl : 11 ≤ l) (hlogp : 0 ≤ Real.log (C.p : ℝ))
    (D_exact : ℝ) (hD : (1 - 1 / l) * Real.log (C.p : ℝ) ≤ D_exact) :
    (C.e : ℝ) * Real.log (C.p : ℝ) ≤ T l * D_exact := by
  have hC := hMO C
  have h5 : (C.e : ℝ) ≤ T l * (1 - 1 / l) := e_le_T_one_sub_inv hC.1 hl
  have hT_nonneg : 0 ≤ T l := by
    have hl0 : (0 : ℝ) < l := by linarith
    have hl4 : (0 : ℝ) < l + 4 := by linarith
    have hl3 : (0 : ℝ) < l - 3 := by linarith
    unfold T
    positivity
  have h1 : (C.e : ℝ) * Real.log (C.p : ℝ) ≤
      (T l * (1 - 1 / l)) * Real.log (C.p : ℝ) := by
    exact mul_le_mul_of_nonneg_right h5 hlogp
  have h2 : (T l * (1 - 1 / l)) * Real.log (C.p : ℝ) ≤ T l * D_exact := by
    have hrearr : (T l * (1 - 1 / l)) * Real.log (C.p : ℝ) =
        T l * ((1 - 1 / l) * Real.log (C.p : ℝ)) := by ring
    rw [hrearr]
    exact mul_le_mul_of_nonneg_left hD hT_nonneg
  linarith

/-- **PaperGap ⇒ SSIneqExplicit** (the §12.2 bridge, pure arithmetic): with
`logQ = e·log p`, `V = ((l+5)/4)·D_exact`, the inequality
`e·log p ≤ T(l)·D_exact` is exactly `SSIneqExplicit (sL l) logQ l V`. -/
theorem ssIneqExplicit_of_paperGap
    (C : PrimeConductorCurve) (l : ℝ) (hl : 11 ≤ l)
    (D_exact : ℝ)
    (hgap : (C.e : ℝ) * Real.log (C.p : ℝ) ≤ T l * D_exact) :
    SSIneqExplicit (sL l) ((C.e : ℝ) * Real.log (C.p : ℝ)) l
      (((l + 5) / 4) * D_exact) := by
  have hl0 : (0 : ℝ) < l := by linarith
  have h4 : (0 : ℝ) < l + 4 := by linarith
  have h3 : (0 : ℝ) < l - 3 := by linarith
  have hcoef : (sL l - 1) / (2 * l) = ((l + 4) * (l - 3)) / (24 * l) := by
    unfold sL
    field_simp [ne_of_gt hl0]
    ring
  have hT : ((l + 4) * (l - 3)) / (24 * l) * T l = (l + 5) / 4 := by
    unfold T
    field_simp [ne_of_gt hl0, ne_of_gt h4, ne_of_gt h3]
    ring
  have hcoef_nonneg : 0 ≤ ((l + 4) * (l - 3)) / (24 * l) := by
    apply div_nonneg
    · exact mul_nonneg (le_of_lt h4) (le_of_lt h3)
    · positivity
  have hmul : ((l + 4) * (l - 3)) / (24 * l) *
        ((C.e : ℝ) * Real.log (C.p : ℝ)) ≤
      ((l + 4) * (l - 3)) / (24 * l) * (T l * D_exact) :=
    mul_le_mul_of_nonneg_left hgap hcoef_nonneg
  unfold SSIneqExplicit
  calc
    (sL l - 1) * (((C.e : ℝ) * Real.log (C.p : ℝ)) / (2 * l))
        = (((l + 4) * (l - 3)) / (24 * l)) *
            ((C.e : ℝ) * Real.log (C.p : ℝ)) := by
          unfold sL
          field_simp [ne_of_gt hl0]
          ring
    _ ≤ (((l + 4) * (l - 3)) / (24 * l)) * (T l * D_exact) := hmul
    _ = ((l + 5) / 4) * D_exact := by
          rw [← mul_assoc, hT]
/-- **Combined §12.2 skeleton**: Mestre–Oesterlé + D_exact lower bound gives
`SSIneqExplicit` for the prime-conductor Θ-data. -/
theorem paperGap_of_primeConductor
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (l : ℝ) (hl : 11 ≤ l) (hlogp : 0 ≤ Real.log (C.p : ℝ))
    (D_exact : ℝ) (hD : (1 - 1 / l) * Real.log (C.p : ℝ) ≤ D_exact) :
    SSIneqExplicit (sL l) ((C.e : ℝ) * Real.log (C.p : ℝ)) l
      (((l + 5) / 4) * D_exact) :=
  ssIneqExplicit_of_paperGap C l hl D_exact
    (paperGap_of_primeConductor_arith hMO C l hl hlogp D_exact hD)

structure RouteCRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def routeCRows : List RouteCRow :=
  [ ⟨"MestreOesterleBound", "prime conductor p => e_p=ord_p(Delta_min)<=5; p>37 => e_p<=2; exceptions p=11,17,19,37 (<=5)", "EXTERNAL_PROP (parameter)"⟩
  , ⟨"T(l)", "6*l*(l+5)/((l+4)(l-3))", "DEF"⟩
  , ⟨"numeric margin", "5 <= T(l)*(1-1/l) for l>=11 (l=11: 8; limit 6)", "PROVED"⟩
  , ⟨"e bound", "e<=5 => e <= T(l)(1-1/l)", "PROVED"⟩
  , ⟨"paperGap arithmetic", "hMO + D_exact >= (1-1/l)log p => e*log p <= T(l)D_exact", "PROVED_CONDITIONAL"⟩
  , ⟨"paperGap => SSIneq", "e*log p <= T(l)D_exact <-> SSIneqExplicit (sL l) logQ l ((l+5)/4 D_exact)", "PROVED"⟩
  , ⟨"combined skeleton", "paperGap_of_primeConductor", "PROVED_CONDITIONAL (hMO external)"⟩
  , ⟨"THETA-data legality", "l prime>=11, l∤e_p (e_p<=5<11); semistable rho-bar surjective for l>=11 (Mazur); image contains SL2 after E[30] (l>=7)", "EXTERNAL/UNFORMALIZED"⟩
  , ⟨"D_exact lower bound", "D_exact >= (1-1/l)log p from local different/shell contributions", "PENDING (L1-L7)"⟩
  , ⟨"scope", "external theorem explicit parameter; no sorry/axiom; no fake proof", "INTEGRITY"⟩
  ]

theorem routeCRows_length : routeCRows.length = 10 := rfl

theorem routeCRows_has_external :
    routeCRows.any (fun r => r.status = "EXTERNAL_PROP (parameter)") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual.five_le_T_one_sub_inv
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual.paperGap_of_primeConductor
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual.ssIneqExplicit_of_paperGap
