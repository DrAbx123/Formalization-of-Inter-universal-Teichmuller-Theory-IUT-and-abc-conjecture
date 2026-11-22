import tmp.sheaf.xif.paper.Mzk1P1SpecialSetActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! Mainline: P1(Qbar) point distinctness/injectivity laws (real proofs). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1P1PointLawsActual

open LeanFormal.IUT.XiFPaper.Mzk1P1SpecialSetActual

universe u

theorem P1Point.ofFinite_injective {K : Type u} :
    Function.Injective (P1Point.ofFinite : K → P1Point K) := by
  intro x y h
  simpa [P1Point.ofFinite] using h

theorem P1Point.infty_ne_ofFinite {K : Type u} (x : K) :
    (P1Point.infty : P1Point K) ≠ P1Point.ofFinite x := by
  simp [P1Point.infty, P1Point.ofFinite]

theorem P1Point.ofFinite_ne_infty {K : Type u} (x : K) :
    P1Point.ofFinite x ≠ (P1Point.infty : P1Point K) :=
  Ne.symm (P1Point.infty_ne_ofFinite x)

end LeanFormal.IUT.XiFPaper.Mzk1P1PointLawsActual