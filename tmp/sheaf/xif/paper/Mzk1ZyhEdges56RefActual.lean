import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Adapted Cor312 <-> Thm110 real-arithmetic interface (from zyh20041227 audit)

Reference adaptation (Mathlib 4.32.2, `Real`) of the verified arithmetic layer of
`tmp/online/zyh20041227__abc-iut-formal-audit/.../formalization/lean_edges/{Edge_5,Edge_6}.lean`
(originally Lean 4.33.1 with `Rat`).  The paper calibration is
`C_Theta * |log q| = -|log Theta|` with `|log q| = log q / (2l)`; `E` and `E_req`
are the W5-E quantities `mu^log(H) + A(l)|log q|` and `(A(l)-1)|log q|` with
`A(l) = l(l+1)/12`.

Only the proved arithmetic identities/implications are adapted; deep IUT inputs
(membership/volume inequality, E upper bound, IUT-IV Step (viii)) remain named
parameters in the source and are NOT asserted here.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ZyhEdges56RefActual

noncomputable section

/-- `|log q| = log q / (2l)` ([IUT-IV] p.23; W5-E Section 1.1). -/
def abslogq (logq : Real) (l : Nat) : Real := logq / (2 * (l : Real))

theorem abslogq_pos {logq : Real} {l : Nat} (hlogq : 0 < logq) (hl : 5 ≤ l) :
    0 < abslogq logq l := by
  unfold abslogq
  have hl0 : (0 : Real) < (l : Real) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hl)
  positivity

/-- Edge_5.Data numerical skeleton for the Cor 3.12 situation. -/
structure Cor312Data where
  l : Nat
  hl : 5 ≤ l
  logq : Real
  hlogq : 0 < logq
  logTheta : Real
  CTheta : Real
  hCTheta : CTheta * abslogq logq l = logTheta

/-- `-|log q| = mu^log(Q)`. -/
def volQ (D : Cor312Data) : Real := -abslogq D.logq D.l

/-- A-076 aggregate: `-|log Theta| >= -|log q|` and `C_Theta >= -1`. -/
def A076 (D : Cor312Data) : Prop := D.logTheta ≥ volQ D ∧ D.CTheta ≥ -1

/-- Cor 3.12 log-volume estimate `C_Theta >= -1`. -/
def Cor312 (D : Cor312Data) : Prop := D.CTheta ≥ -1

/-- RE6 Section 3.5 Step 4: from `logTheta <= CTheta * a` and `-a <= logTheta`, `a > 0`, get `CTheta >= -1`. -/
theorem cor312_of_ineq {logTheta CTheta a : Real}
    (hineq : logTheta ≤ CTheta * a) (hvol : -a ≤ logTheta) (ha : 0 < a) :
    -1 ≤ CTheta := by
  have h1 : (-1 : Real) * a ≤ CTheta * a := by
    calc (-1 : Real) * a = -a := by ring
      _ ≤ logTheta := hvol
      _ ≤ CTheta * a := hineq
  exact (le_of_mul_le_mul_right h1 ha)

/-- Edge 5: `A076 -> Cor312` by the calibration and `|log q| > 0`. -/
theorem edge5 (D : Cor312Data) : A076 D → Cor312 D := by
  intro h
  have hineq : D.logTheta ≤ D.CTheta * abslogq D.logq D.l := by
    rw [D.hCTheta]
  exact cor312_of_ineq hineq h.1 (abslogq_pos D.hlogq D.hl)

/-- Cor 3.12 in the `forall C_Theta` form. -/
theorem cor312_forall (D : Cor312Data) (h : A076 D) :
    ∀ c : Real, D.logTheta ≤ c * abslogq D.logq D.l → -1 ≤ c :=
  fun c hc => cor312_of_ineq hc h.1 (abslogq_pos D.hlogq D.hl)

/-- `A(l) = l(l+1)/12` (W5-E Section 1.1). -/
def Acoef (l : Nat) : Real := (l : Real) * ((l : Real) + 1) / 12

/-- Edge_6.Data numerical skeleton for the Thm 1.10 situation. -/
structure Thm110Data where
  l : Nat
  hl : 5 ≤ l
  logq : Real
  hlogq : 0 < logq
  logTheta : Real
  CTheta : Real
  hCTheta : CTheta * abslogq logq l = logTheta
  C : Real
  hC : 0 < C
  logdK : Real
  Sigma : Real

/-- `E = mu^log(H) + A(l)|log q|`. -/
def E (D : Thm110Data) : Real := D.logTheta + Acoef D.l * abslogq D.logq D.l

/-- `E_req = (A(l)-1)|log q|`. -/
def Ereq (D : Thm110Data) : Real := (Acoef D.l - 1) * abslogq D.logq D.l

/-- P1_ineq: `E_req <= E`. -/
def P1ineq (D : Thm110Data) : Prop := Ereq D ≤ E D

/-- Cor 3.12 estimate `C_Theta >= -1` for Thm 1.10 data. -/
def Cor312p (D : Thm110Data) : Prop := -1 ≤ D.CTheta

/-- Thm 1.10 conclusion `log q <= C * log d_K + Sigma`. -/
def Thm110 (D : Thm110Data) : Prop := D.logq ≤ D.C * D.logdK + D.Sigma

/-- R1 identity: `E - E_req = -|log Theta| + |log q|`. -/
theorem E_sub_Ereq (D : Thm110Data) :
    E D - Ereq D = D.logTheta + abslogq D.logq D.l := by
  unfold E Ereq Acoef
  ring

/-- `P1_ineq` from `C_Theta >= -1` (Edge 6 lower-bound step). -/
theorem p1ineq_of_cor312 (D : Thm110Data) (h : Cor312p D) : P1ineq D := by
  have hpos : 0 < abslogq D.logq D.l := abslogq_pos D.hlogq D.hl
  have hC : (-1 : Real) ≤ D.CTheta := h
  have hc : 0 ≤ D.CTheta + 1 := by linarith
  have hprod : 0 ≤ (D.CTheta + 1) * abslogq D.logq D.l :=
    mul_nonneg hc (le_of_lt hpos)
  have hsub : E D - Ereq D = (D.CTheta + 1) * abslogq D.logq D.l := by
    rw [E_sub_Ereq, ← D.hCTheta]
    ring
  have hnonneg : 0 ≤ E D - Ereq D := by rw [hsub]; exact hprod
  unfold P1ineq
  linarith

/-- `C_Theta >= -1` from `P1_ineq` (converse, Edge 6). -/
theorem cor312_of_p1ineq (D : Thm110Data) (h : P1ineq D) : Cor312p D := by
  have hpos : 0 < abslogq D.logq D.l := abslogq_pos D.hlogq D.hl
  have hsub : E D - Ereq D = (D.CTheta + 1) * abslogq D.logq D.l := by
    rw [E_sub_Ereq, ← D.hCTheta]
    ring
  have hnonneg : 0 ≤ (D.CTheta + 1) * abslogq D.logq D.l := by
    unfold P1ineq at h
    rw [← hsub]
    linarith
  have hC1 : 0 ≤ D.CTheta + 1 := by
    by_contra hneg
    have hlt : (D.CTheta + 1) * abslogq D.logq D.l < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos
    linarith
  unfold Cor312p
  linarith

/-- Equivalence under the calibration. -/
theorem cor312_iff_p1ineq (D : Thm110Data) : Cor312p D ↔ P1ineq D :=
  ⟨p1ineq_of_cor312 D, cor312_of_p1ineq D⟩

end

end LeanFormal.IUT.XiFPaper.Mzk1ZyhEdges56RefActual
