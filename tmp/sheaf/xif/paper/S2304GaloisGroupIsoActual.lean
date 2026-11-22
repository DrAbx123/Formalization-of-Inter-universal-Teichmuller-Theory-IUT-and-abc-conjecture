import tmp.sheaf.xif.paper.S2301DegreeEqOrderActual
import tmp.sheaf.xif.paper.S2289QE5DegreeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2304GaloisGroupIsoActual

open LeanFormal.IUT.XiFPaper.S2301DegreeEqOrderActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2298QE5OrderActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open Polynomial

/-- The polynomial Galois group of psi5. -/
abbrev S2304Gal : Type := Polynomial.Gal S2057Psi5Q

/-- Actual cardinality of the polynomial Galois group: it equals the degree
of the splitting field. -/
theorem S2304Gal_card_eq_finrank :
    Nat.card S2304Gal = Module.finrank ℚ s2289QE5 :=
  Polynomial.Gal.card_of_separable S2057Psi5Q_separable

/-- Exact Galois-group/image isomorphism structure, with the polynomial
Galois group as the source. -/
structure S2304GaloisGroupIsoImage (H : Subgroup GL2) where
  iso : S2304Gal ≃* H

/-- Exact required statement. -/
def S2304GaloisGroupIsoImageRequired (H : Subgroup GL2) : Prop :=
  Nonempty (S2304GaloisGroupIsoImage H)

/-- From an iso, the image order is the degree of Q(E[5]). -/
theorem S2304Degree_eq_imageOrder_of_iso
    (H : Subgroup GL2) (D : S2304GaloisGroupIsoImage H) :
    Module.finrank ℚ s2289QE5 = Nat.card H := by
  rw [← S2304Gal_card_eq_finrank]
  exact Nat.card_congr D.iso.toEquiv

/-- Exact first missing conjunction with the S2301 form. -/
def S2304ExactFirstMissing (H : Subgroup GL2) : Prop :=
  S2304GaloisGroupIsoImageRequired H

end LeanFormal.IUT.XiFPaper.S2304GaloisGroupIsoActual

end
