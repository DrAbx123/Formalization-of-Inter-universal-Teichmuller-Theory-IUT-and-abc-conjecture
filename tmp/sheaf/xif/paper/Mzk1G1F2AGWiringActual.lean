/- F2.1 item1 (function field / places wiring) for the Fermat curve. REUSE:
- `AG01CurveFoundationsActual.S3133CurveOver` (proper/smooth/geometrically connected curve),
- `AG04bResidueFieldActual.agResidueClass`/`agSectionResidue` (residue fields at points),
- `Mzk1G1FermatCurveToSpecActual.fermatCurveToSpec` / `...FermatPiProperActual.fermatCurveToSpec_isProper_final`,
- `Mzk1G1FermatCurveSmoothFinalActual.fermatCurveToSpec_smoothOfRelativeDimension` (DONE 17:40),
- `Mzk1G1A3CurveIntegralActual.curve_isIntegral` / `Mzk1G1A3FunctionFieldFinalActual.curve_locallyNoetherian`.
MISSING INSTANCE (registered, not faked): `GeometricallyConnected (fermatCurveToSpec n)` — the
general algebraically-closed-fibre connectivity (only the fixed `kbar` case is available). -/
import tmp.sheaf.xif.paper.AG01CurveFoundationsActual
import tmp.sheaf.xif.paper.AG04bResidueFieldActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveToSpecActual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiProperActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveSmoothFinalActual
import tmp.sheaf.xif.paper.Mzk1G1A3CurveIntegralActual
import tmp.sheaf.xif.paper.Mzk1G1A3FunctionFieldFinalActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2AGWiringActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveToSpecActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiProperActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmoothFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3CurveIntegralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3FunctionFieldFinalActual
open LeanFormal.IUT.XiFPaper.AG01CurveFoundationsActual
open LeanFormal.IUT.XiFPaper.AG04bResidueFieldActual

/-- The Fermat curve as a scheme over `Spec ℚ`. -/
abbrev fermatCurveOver (n : Nat) : Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk (fermatCurveToSpec n)

/-- Properness of `Y_n → Spec ℚ`. -/
theorem fermatCurveOver_isProper (n : Nat) (hn : 0 < n) :
    IsProper (fermatCurveOver n).hom :=
  fermatCurveToSpec_isProper_final n hn

/-- Smoothness of `Y_n → Spec ℚ` (from graceful relative-dimension-one smoothness). -/
theorem fermatCurveOver_smooth (n : Nat) (hn : 0 < n) :
    Smooth (fermatCurveToSpec n) :=
  (fermatCurveToSpec_smoothOfRelativeDimension n hn).smooth

/-- Relative-dimension-one smoothness of `Y_n → Spec ℚ`. -/
theorem fermatCurveOver_smoothOfRelativeDimension (n : Nat) (hn : 0 < n) :
    SmoothOfRelativeDimension 1 (fermatCurveToSpec n) :=
  fermatCurveToSpec_smoothOfRelativeDimension n hn

/-- Integrality of the Fermat curve. -/
theorem fermatCurve_isIntegral (n : Nat) (hn : 0 < n) :
    IsIntegral (fermatCurveScheme n) :=
  curve_isIntegral n hn

/-- Local noetherianity of the Fermat curve. -/
theorem fermatCurve_isLocallyNoetherian (n : Nat) :
    IsLocallyNoetherian (fermatCurveScheme n) :=
  curve_locallyNoetherian n

/-- The Fermat curve as an `S3133CurveOver ℚ`; geometric connectedness is the remaining
explicit obligation. -/
noncomputable def fermatCurveStructure (n : Nat) (hn : 0 < n)
    (hgc : GeometricallyConnected (fermatCurveToSpec n)) :
    S3133CurveOver ℚ where
  X := fermatCurveOver n
  proper := fermatCurveOver_isProper n hn
  smooth := fermatCurveOver_smooth n hn
  geomConnected := hgc
  relativeDimOne := fermatCurveOver_smoothOfRelativeDimension n hn

/-- The AG residue-class map is available on the Fermat curve. -/
theorem fermatCurve_agResidueClass_apply (n : Nat) (hn : 0 < n)
    (x : fermatCurveScheme n)
    (y : (fermatCurveScheme n).presheaf.stalk x) :
    agResidueClass (X := fermatCurveScheme n) x y =
      IsLocalRing.residue ((fermatCurveScheme n).presheaf.stalk x) y := by
  haveI : IsIntegral (fermatCurveScheme n) := curve_isIntegral n hn
  haveI : IsLocallyNoetherian (fermatCurveScheme n) := curve_locallyNoetherian n
  exact agResidueClass_apply x y

#print axioms fermatCurveOver_isProper
#print axioms fermatCurveOver_smooth
#print axioms fermatCurveOver_smoothOfRelativeDimension
#print axioms fermatCurveStructure
#print axioms fermatCurve_agResidueClass_apply
end LeanFormal.IUT.XiFPaper.Mzk1G1F2AGWiringActual
