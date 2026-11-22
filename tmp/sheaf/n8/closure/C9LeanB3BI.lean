import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Conditional P6 for the b=3 B=I profile

Task-268 abstract Lean formalization.  The profile carries the conditional
C1/TC/CFTH hypotheses, the finite-plus-archimedean lower bound

  h_C >= H_p^Sp log p + h_inf,

the b=3 B=I finite value H_p^Sp=9/41, and Q_p=(-3/41)log p.  The archimedean
threshold is

  h_inf >= -S3 = -(12/41)log p.

Then h_C >= Q_p, i.e. P6 holds for this conditional profile.  The numerical
values are the B=I b=3 profile values; no arbitrary parameter is chosen.

No axiom or sorry is used.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.N8Closure.C9LeanB3BI

/-- Conditional data for the b=3 B=I profile.  The fields `C1`, `TC`, `CFTH`
are the source/target conditions under which the finite-plus-archimedean
bound is available; their proofs are kept explicit. -/
structure B3BIProfile where
  p : ℝ
  hp : 1 < p
  C1 : Prop
  TC : Prop
  CFTH : Prop
  hC1 : C1
  hTC : TC
  hCFTH : CFTH
  hC : ℝ
  hInf : ℝ
  hC_ge : hC ≥ (9 / 41 : ℝ) * Real.log p + hInf
  hInf_ge : hInf ≥ -(12 / 41 : ℝ) * Real.log p

/-- The B=I b=3 finite term `H_p^Sp log p = (9/41) log p`. -/
noncomputable def HpSpLog (P : B3BIProfile) : ℝ :=
  (9 / 41 : ℝ) * Real.log P.p

/-- The b=3 B=I q-pilot value `Q_p = (-3/41) log p`. -/
noncomputable def Qp (P : B3BIProfile) : ℝ :=
  (-3 / 41 : ℝ) * Real.log P.p

/-- The threshold quantity `S3 = (12/41) log p`. -/
noncomputable def S3 (P : B3BIProfile) : ℝ :=
  (12 / 41 : ℝ) * Real.log P.p

theorem Qp_eq (P : B3BIProfile) : Qp P = (-3 / 41 : ℝ) * Real.log P.p := rfl

theorem S3_eq (P : B3BIProfile) : S3 P = (12 / 41 : ℝ) * Real.log P.p := rfl

theorem HpSpLog_eq (P : B3BIProfile) : HpSpLog P = (9 / 41 : ℝ) * Real.log P.p := rfl

/-- The finite-plus-archimedean lower bound with the B=I b=3 finite term. -/
theorem hC_ge_HpSpLog_add_hInf (P : B3BIProfile) :
    P.hC ≥ HpSpLog P + P.hInf :=
  P.hC_ge

/-- `h_inf >= -S3` is the stated archimedean threshold. -/
theorem hInf_ge_threshold_iff (P : B3BIProfile) :
    P.hInf ≥ -S3 P ↔ P.hInf ≥ -(12 / 41 : ℝ) * Real.log P.p := by
  unfold S3
  ring_nf

/-- Conditional P6 for the b=3 B=I profile: if the finite-plus-archimedean
bound and the threshold hold, then `h_C >= Q_p`. -/
theorem b3BI_conditional_P6 (P : B3BIProfile) : P.hC ≥ Qp P := by
  have hL : (9 / 41 : ℝ) * Real.log P.p + P.hInf ≥ (-3 / 41 : ℝ) * Real.log P.p := by
    have := P.hInf_ge
    linarith
  calc
    P.hC ≥ (9 / 41 : ℝ) * Real.log P.p + P.hInf := P.hC_ge
    _ ≥ (-3 / 41 : ℝ) * Real.log P.p := hL
    _ = Qp P := by rw [Qp]

/-- The unconditional algebraic core of the conditional theorem. -/
theorem b3BI_core (p hC hInf : ℝ)
    (hbound : hC ≥ (9 / 41 : ℝ) * Real.log p + hInf)
    (hth : hInf ≥ -(12 / 41 : ℝ) * Real.log p) :
    hC ≥ (-3 / 41 : ℝ) * Real.log p := by
  have h : (9 / 41 : ℝ) * Real.log p + hInf ≥ (-3 / 41 : ℝ) * Real.log p := by
    linarith
  linarith [hbound, h]

end LeanFormal.IUT.N8Closure.C9LeanB3BI

end