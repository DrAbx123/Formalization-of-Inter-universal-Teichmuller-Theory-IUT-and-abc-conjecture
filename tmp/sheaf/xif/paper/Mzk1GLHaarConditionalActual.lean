/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1GLActBundlingActual

/-!
# General GL_d(Z_p) Haar invariance: exact condition placeholder (GAP)

`glAct` is packed as a Q_p-linear map in `Mzk1GLActBundlingActual`.
The actual Haar-uniqueness proof is not available here because the additive
`addHaarScalarFactor`/`measure_isAddInvariant_eq_smul_of_isCompact_closure`
names do not resolve in this olean context.  This file records the exact
condition (measure preservation) without pretending to prove it. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1GLHaarConditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1GLActBundlingActual
open LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [MeasurableSpace (d → ℚ_[p])]
/-- Exact missing statement: `glAct V` preserves the Haar measure `μ`. -/
def GLHaarInvarianceCondition (V : Matrix d d (PadicInt p))
    (μ : Measure (d → ℚ_[p])) : Prop :=
  μ.map (glAct p d V) = μ
theorem glHaarInvarianceCondition_iff (V : Matrix d d (PadicInt p))
    (μ : Measure (d → ℚ_[p])) :
    GLHaarInvarianceCondition V μ ↔ μ.map (glAct p d V) = μ := Iff.rfl
def glHaarRows : List (String × String) :=
  [ ("GLHaarInvarianceCondition", "exact condition, GAP"),
    ("c=1 / Haar uniqueness", "GAP") ]
theorem glHaarRows_length : glHaarRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1GLHaarConditionalActual
