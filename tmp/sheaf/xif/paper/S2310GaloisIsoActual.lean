import tmp.sheaf.xif.paper.S2304GaloisGroupIsoActual
import Mathlib.FieldTheory.PolynomialGaloisGroup

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2310GaloisIsoActual

open LeanFormal.IUT.XiFPaper.S2304GaloisGroupIsoActual
open LeanFormal.IUT.XiFPaper.S2301DegreeEqOrderActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
open LeanFormal.IUT.XiFPaper.S2298QE5OrderActual
open LeanFormal.IUT.XiFPaper.S2294QE5DegreeValueActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open Polynomial

/-- The faithful action of the polynomial Galois group on the twelve roots of
psi5 in the splitting field Q(E[5]). -/
noncomputable def S2310RootAction :
    S2304Gal →* Equiv.Perm (S2057Psi5Q.rootSet s2289QE5) :=
  letI : Fact ((S2057Psi5Q.map (algebraMap ℚ s2289QE5)).Splits) :=
    ⟨Polynomial.SplittingField.splits S2057Psi5Q⟩
  Polynomial.Gal.galActionHom S2057Psi5Q s2289QE5

/-- The root action is faithful. -/
theorem S2310RootAction_injective :
    Function.Injective S2310RootAction := by
  letI : Fact ((S2057Psi5Q.map (algebraMap ℚ s2289QE5)).Splits) :=
    ⟨Polynomial.SplittingField.splits S2057Psi5Q⟩
  unfold S2310RootAction
  exact Polynomial.Gal.galActionHom_injective S2057Psi5Q s2289QE5

/-- The image of the Galois group in the permutation group of the twelve
roots. -/
noncomputable def S2310RootActionImage :
    Subgroup (Equiv.Perm (S2057Psi5Q.rootSet s2289QE5)) :=
  S2310RootAction.range

/-- Exact missing structure: the actual mod-5 image subgroup is isomorphic
to the polynomial Galois group of psi5. -/
structure S2310GaloisImageIso (H : Subgroup GL2) where
  iso : S2304Gal ≃* H

/-- Exact required statement. -/
def S2310GaloisImageIsoRequired (H : Subgroup GL2) : Prop :=
  Nonempty (S2310GaloisImageIso H)

/-- Conditional degree formula from the exact iso. -/
theorem S2310Degree_eq_imageOrder_of_iso
    (H : Subgroup GL2) (D : S2310GaloisImageIso H) :
    Module.finrank ℚ s2289QE5 = Nat.card H := by
  rw [s2294QE5_finrank_eq_card_aut]
  exact Nat.card_congr D.iso.toEquiv

/-- Conditional degree 480 from the exact iso and image hypotheses. -/
theorem S2310Degree_eq_480_of_iso_and_hypotheses
    (H : Subgroup GL2) (D : S2310GaloisImageIso H)
    (hdet : DetSurjectiveOn H) (htrans : PairTransitive H)
    (h102 : HasCycleType102 H) :
    Module.finrank ℚ s2289QE5 = 480 := by
  rw [S2310Degree_eq_imageOrder_of_iso H D]
  exact S2298ImageCard_eq_480_of_hypotheses H hdet htrans h102

end LeanFormal.IUT.XiFPaper.S2310GaloisIsoActual

end
