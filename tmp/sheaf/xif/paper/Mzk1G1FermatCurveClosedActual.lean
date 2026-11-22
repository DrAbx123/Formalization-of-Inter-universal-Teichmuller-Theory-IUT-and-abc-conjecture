import tmp.sheaf.xif.paper.Mzk1G1FermatProjectiveScheme4Actual
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveClosedActual
open MvPolynomial AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjectiveScheme4Actual
/-- Fermat closed subset as `Closeds` of the ambient Proj. -/
noncomputable def fermatCurveCloseds (n : Nat) :
    TopologicalSpace.Closeds fermatProjectivePlane :=
  ⟨fermatClosedSubset n, fermatClosedSubset_isClosed n⟩
/-- Vanishing ideal sheaf of the Fermat closed subset. -/
noncomputable def fermatCurveIdealSheaf (n : Nat) :
    fermatProjectivePlane.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (fermatCurveCloseds n)
/-- Actual Fermat curve closed subscheme. -/
noncomputable def fermatCurveClosedSubscheme (n : Nat) : Scheme :=
  (fermatCurveIdealSheaf n).subscheme
/-- Closed immersion into the ambient projective plane. -/
noncomputable def fermatCurveClosedImmersion (n : Nat) :
    fermatCurveClosedSubscheme n ⟶ fermatProjectivePlane :=
  (fermatCurveIdealSheaf n).subschemeι
theorem fermatCurveClosedImmersion_isClosed (n : Nat) :
    IsClosedImmersion (fermatCurveClosedImmersion n) :=
  inferInstance
theorem fermatCurveClosedImmersion_isProper (n : Nat) :
    IsProper (fermatCurveClosedImmersion n) :=
  (IsClosedImmersion.iff_isProper_and_mono.mp
    (fermatCurveClosedImmersion_isClosed n)).1
#print axioms fermatCurveClosedImmersion_isClosed
#print axioms fermatCurveClosedImmersion_isProper
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveClosedActual
end