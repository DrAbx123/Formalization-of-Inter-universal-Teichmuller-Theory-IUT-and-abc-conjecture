import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-!
  Mainline: additive re-freeze route consumers (the refuted frontier routes are
  blocked; the additive V2 form remains an equivalent re-statement of ABC).
  Re-exports only: no new math, no sorry/axiom.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1AdditiveRefreezeRouteActual

open LeanFormal.IUT

/-- ABC follows from the additive height-weight form (V2), by the proved equivalence. -/
theorem abcConjecture_of_additiveV2 (h : ABCHeightWeightAdditiveBoundV2) :
    ABCConjecture :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr h

/-- Conversely ABC gives the additive V2 form. -/
theorem additiveV2_of_abcConjecture (h : ABCConjecture) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp h

/-- ABC iff its logarithmic form (via the proved equivalence in IUTToABC). -/
theorem abcConjecture_iff_abcLogConjecture_reexport :
    ABCConjecture ↔ ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture

end LeanFormal.IUT.XiFPaper.Mzk1AdditiveRefreezeRouteActual