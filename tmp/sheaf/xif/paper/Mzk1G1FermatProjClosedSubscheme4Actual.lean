import tmp.sheaf.xif.paper.Mzk1G1FermatProjectiveScheme4Actual
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjClosedSubscheme4Actual
open MvPolynomial AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjectiveScheme4Actual
noncomputable abbrev fermatCloseds (n : Nat) :
    TopologicalSpace.Closeds fermatProjectivePlane :=
  ⟨fermatClosedSubset n, fermatClosedSubset_isClosed n⟩
noncomputable abbrev fermatIdealSheaf (n : Nat) : fermatProjectivePlane.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (fermatCloseds n)
noncomputable abbrev fermatCurveScheme (n : Nat) : Scheme :=
  (fermatIdealSheaf n).subscheme
noncomputable abbrev fermatCurveImmersion (n : Nat) :
    fermatCurveScheme n ⟶ fermatProjectivePlane :=
  (fermatIdealSheaf n).subschemeι
theorem fermatCurveImmersion_isClosedImmersion (n : Nat) :
    IsClosedImmersion (fermatCurveImmersion n) :=
  inferInstance
theorem fermatCurveImmersion_isProper (n : Nat) :
    IsProper (fermatCurveImmersion n) :=
  ((IsClosedImmersion.iff_isProper_and_mono (f := fermatCurveImmersion n)).mp
    (fermatCurveImmersion_isClosedImmersion n)).1
#print axioms fermatCurveImmersion_isClosedImmersion
#print axioms fermatCurveImmersion_isProper
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjClosedSubscheme4Actual
end