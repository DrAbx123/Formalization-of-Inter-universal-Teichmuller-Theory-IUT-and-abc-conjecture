import tmp.sheaf.xif.paper.S1433KernelCardPortActual
import tmp.sheaf.xif.paper.S1430MulByIntBasicActual
import tmp.sheaf.xif.paper.S1466MulByIntDegreeActual

/-! # S1478: geometric torsion card retry

Checked layers:

* S1465: minimal Isogeny/psiFunctionField port (available).
* S1466: degree / separable-degree layer (available).
* S1467: generic point / fieldPullback layer (olean available).
* S1433: exact geometric torsion first field and the ported reduction.

The TauCeti geometric count still cannot be closed:

* S1465 does not construct mulByIntIsogeny; it only gives the minimal Isogeny
  structure and psi/phi function-field elements.
* S1467 gives fieldPullback for an arbitrary Isogeny and the generic point,
  but not the tautological point or the zsmul generic-point identity.
* The first missing source lemma remains EquationMulByInt (the [n] equation),
  needed before mulByIntIsogeny and hence before any kernel count.

This file records the exact first missing fields without asserting the count.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1478GeometricTorsionPortActual

open WeierstrassCurve WeierstrassCurve.Affine
open LeanFormal.IUT.XiFPaper.S1433KernelCardPortActual

universe u
variable {F : Type u} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F)

/-- Exact first missing source lemma: the [n] equation for the multiplication
map, before mulByIntIsogeny or any kernel count. -/
abbrev S1478EquationMulByIntFirstField (n : Int) : Prop :=
  TauCeti.Isogeny.EquationMulByInt W n

/-- Exact geometric torsion first field: the count over the algebraic closure. -/
abbrev S1478GeometricTorsionCardFirstField (n : Int) : Prop :=
  S1433GeometricTorsionCard W n

/-- The [n]-equation first field is exactly the S1430 named proposition. -/
theorem s1478EquationMulByIntFirstField_iff (n : Int) :
    S1478EquationMulByIntFirstField W n ↔
      TauCeti.Isogeny.EquationMulByInt W n :=
  Iff.rfl

/-- The geometric first field is exactly the S1433 geometric count. -/
theorem s1478GeometricTorsionCardFirstField_iff (n : Int) :
    S1478GeometricTorsionCardFirstField W n ↔ S1433GeometricTorsionCard W n :=
  Iff.rfl

-- Actual donor checks: the degree/separability layer and the generic-point
-- pullback layer exist, but neither supplies the [n] equation or the kernel
-- lower bound.
#check WeierstrassCurve.isogenySeparableDegree_eq_natAbs_sq_of_degree
#check WeierstrassCurve.isogenySeparableDegree_mul_inseparableDegree

end LeanFormal.IUT.XiFPaper.S1478GeometricTorsionPortActual

end
