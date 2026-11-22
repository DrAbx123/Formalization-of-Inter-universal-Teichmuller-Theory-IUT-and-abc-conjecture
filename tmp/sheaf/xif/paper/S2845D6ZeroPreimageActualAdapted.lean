import tmp.sheaf.xif.paper.S2844D6F6BaseChangeActual
import tmp.sheaf.xif.paper.S2832ChartZPointAtInfinityNoGoActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2832ChartZPointAtInfinityNoGoActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2845D6ZeroPreimageActualAdapted

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field K := inferInstance
local instance : DecidableEq K := Classical.decEq _
local instance : NumberField K := LeanFormal.IUT.XiFPaper.S2809E6FiniteActual.S2809_numberField

/-- The infinity morphism maps to the zero projective point under the glued map. -/
theorem S2845_gluedMap_infinity_eq_zero :
    S2844GluedMap (S2844InfinityOver (K := K)).left = 0 := by
  classical
  unfold S2844GluedMap
  split_ifs with h
  · exact absurd (by simpa [S2844InfinityOver, S2832PointAtInfinityMorphism] using h)
      S2832_no_chartZ_map_to_pointAtInfinity K
  · rfl

/-- D6 zero preimage is actual. -/
theorem S2845ZeroPreimage : S2844ZeroPreimage :=
  ⟨S2844InfinityOver, S2845_gluedMap_infinity_eq_zero⟩

/-- Conditional curve-point realization becomes actual. -/
noncomputable def S2845CurvePointRealization :
    S2813CurvePointRealization K S2844X S2844Punctured :=
  S2844CurvePointRealization S2845ZeroPreimage

#check S2845_gluedMap_infinity_eq_zero
#check S2845ZeroPreimage
#check S2845CurvePointRealization
#print axioms S2845_gluedMap_infinity_eq_zero
#print axioms S2845ZeroPreimage
#print axioms S2845CurvePointRealization

end LeanFormal.IUT.XiFPaper.S2845D6ZeroPreimageActualAdapted
end