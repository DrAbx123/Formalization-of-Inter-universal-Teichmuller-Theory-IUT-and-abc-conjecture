import tmp.sheaf.xif.paper.S2298QE5OrderActual
import tmp.sheaf.xif.paper.S2294QE5DegreeValueActual
import tmp.sheaf.xif.paper.S2055DicksonClassActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2301DegreeEqOrderActual

open LeanFormal.IUT.XiFPaper.S2298QE5OrderActual
open LeanFormal.IUT.XiFPaper.S2294QE5DegreeValueActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
open LeanFormal.IUT.XiFPaper.S2055DicksonClassActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual

/-- Exact Galois-correspondence input: the absolute Galois group of Q(E[5])
is isomorphic to the actual mod-5 image subgroup H. -/
structure S2301GaloisGroupIsoImage (H : Subgroup GL2) where
  iso : (s2289QE5 ≃ₐ[ℚ] s2289QE5) ≃* H

/-- From the isomorphism, the degree of Q(E[5]) equals the image order. -/
theorem S2301Degree_eq_imageOrder_of_iso
    (H : Subgroup GL2) (D : S2301GaloisGroupIsoImage H) :
    Module.finrank ℚ s2289QE5 = Nat.card H := by
  rw [s2294QE5_finrank_eq_card_aut]
  exact Nat.card_congr D.iso.toEquiv

/-- Exact first missing: a multiplicative isomorphism between the absolute
Galois group of Q(E[5]) and the actual mod-5 image subgroup H. -/
def S2301GaloisGroupIsoImageRequired (H : Subgroup GL2) : Prop :=
  Nonempty (S2301GaloisGroupIsoImage H)

/-- From an isomorphism and the image-order hypotheses, the exact degree is
480. -/
theorem S2301Degree_eq_480_of_iso_and_hypotheses
    (H : Subgroup GL2) (D : S2301GaloisGroupIsoImage H)
    (hdet : DetSurjectiveOn H) (htrans : PairTransitive H)
    (h102 : HasCycleType102 H) :
    Module.finrank ℚ s2289QE5 = 480 := by
  rw [S2301Degree_eq_imageOrder_of_iso H D]
  exact S2298ImageCard_eq_480_of_hypotheses H hdet htrans h102

end LeanFormal.IUT.XiFPaper.S2301DegreeEqOrderActual

end
