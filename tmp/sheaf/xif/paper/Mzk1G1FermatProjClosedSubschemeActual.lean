import tmp.sheaf.xif.paper.Mzk1G1FermatProjectiveSchemeActual
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjClosedSubschemeActual
open MvPolynomial AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjectiveSchemeActual
/-- The Fermat closed subset as a `Closeds` of the ambient projective plane. -/
noncomputable def fermatCloseds (n : Nat) :
    TopologicalSpace.Closeds (fermatProjectivePlane (u := 0)) :=
  ⟨fermatClosedSubset (u := 0) n, fermatClosedSubset_isClosed (u := 0) n⟩
/-- The ideal sheaf of the Fermat closed subset. -/
noncomputable def fermatIdealSheaf (n : Nat) :
    (fermatProjectivePlane (u := 0)).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (fermatCloseds n)
/-- The actual Fermat curve as the closed subscheme of the projective plane. -/
noncomputable def fermatCurveScheme (n : Nat) : Scheme :=
  (fermatIdealSheaf n).subscheme
/-- The closed immersion of the Fermat curve into the projective plane. -/
noncomputable def fermatCurveImmersion (n : Nat) :
    fermatCurveScheme n ⟶ fermatProjectivePlane (u := 0) :=
  (fermatIdealSheaf n).subschemeι
/-- The Fermat curve immersion is a closed immersion. -/
theorem fermatCurveImmersion_isClosedImmersion (n : Nat) :
    IsClosedImmersion (fermatCurveImmersion n) :=
  inferInstance
/-- Properness of the Fermat curve immersion, from closed immersion. -/
theorem fermatCurveImmersion_isProper (n : Nat) :
    IsProper (fermatCurveImmersion n) :=
  (IsClosedImmersion.iff_isProper_and_mono.mp (fermatCurveImmersion_isClosedImmersion n)).1
#print axioms fermatCurveImmersion_isClosedImmersion
#print axioms fermatCurveImmersion_isProper
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjClosedSubschemeActual
end