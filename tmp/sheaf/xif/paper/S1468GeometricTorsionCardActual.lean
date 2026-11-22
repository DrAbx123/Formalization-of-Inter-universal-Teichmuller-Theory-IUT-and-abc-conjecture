import tmp.sheaf.xif.paper.S1433KernelCardPortActual
import tmp.sheaf.xif.paper.S1430MulByIntBasicActual

/-! # S1468: geometric torsion card port

Checked prerequisite layer files:

* S1465, S1466, S1467 are absent.
* S1430 (mul-by-int basic), S1431 (degree/separable degree), S1432
  (function field/generic point) are present.

Consequently the TauCeti card_ker_mulByIntIsogeny_of_torsion_rational cannot
be ported completely here: its two remaining ingredients,
card_ker_le_separableDegree and card_emb_mulByIntIsogeny_le_card_ker, are not
in S1430-S1432.  The exact first field is S1433GeometricTorsionCard.

This file ports the source lemma ne_zero_of_psiFunctionField_ne_zero and
records the exact first field and its consumer.  No fake count is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1468GeometricTorsionCardActual

open WeierstrassCurve WeierstrassCurve.Affine
open LeanFormal.IUT.XiFPaper.S1433KernelCardPortActual

universe u
variable {F : Type u} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F)

/-- Port of TauCeti KernelCard line 93: a nonzero division polynomial forces a
nonzero index. -/
theorem s1468_ne_zero_of_psiFunctionField_ne_zero {n : Int}
    (hn : TauCeti.Isogeny.psiFunctionField W n ≠ 0) : n ≠ 0 := by
  rintro rfl
  exact hn (by
    simp [TauCeti.Isogeny.psiFunctionField_def, WeierstrassCurve.ψ_zero])

/-- Exact first field: the geometric torsion cardinality over the algebraic
closure. -/
def S1468GeometricTorsionCardFirstField (n : Int) : Prop :=
  S1433GeometricTorsionCard W n

/-- The exact first field is exactly where the TauCeti kernel count lands. -/
theorem s1468GeometricTorsionCardFirstField_iff (n : Int) :
    S1468GeometricTorsionCardFirstField W n ↔ S1433GeometricTorsionCard W n :=
  Iff.rfl

/-- Consumer: geometric card plus rationality gives the ported kernel card. -/
theorem s1468KernelCard_of_geometricTorsionCard
    {n : Int} (hrat : S1433TorsionRational W n)
    (hgeo : S1468GeometricTorsionCardFirstField W n) :
    S1433KernelCard W n :=
  s1433KernelCard_of_torsionRational_of_geometricTorsionCard hrat hgeo

/-- Consumer in the algebraically closed case. -/
theorem s1468KernelCard_of_isAlgClosed_of_geometricTorsionCard
    [IsAlgClosed F] {n : Int}
    (hgeo : S1468GeometricTorsionCardFirstField W n) :
    S1433KernelCard W n :=
  s1433KernelCard_of_isAlgClosed_of_geometricTorsionCard hgeo

end LeanFormal.IUT.XiFPaper.S1468GeometricTorsionCardActual

end
