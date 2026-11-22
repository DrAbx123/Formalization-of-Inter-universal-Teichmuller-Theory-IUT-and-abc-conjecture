import tmp.sheaf.xif.paper.S2511InfinityPointUB

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
open LeanFormal.IUT.XiFPaper.S2505AwayEquivActual
open LeanFormal.IUT.XiFPaper.S2508CuspDataUB
open LeanFormal.IUT.XiFPaper.S2511InfinityPointUB

local instance : Field UB := inferInstance
local instance : CommRing UB := inferInstance

/-! The frozen target type, re-checked from the compiled olean. -/
#check @LeanFormal.IUT.XiFPaper.S2511InfinityPointUB.S2511Point
#check @LeanFormal.IUT.XiFPaper.S2511InfinityPointUB.S2511Point.left
#check @LeanFormal.IUT.XiFPaper.S2511InfinityPointUB.S2511pointMap

example : S2508ResidueScheme ⟶ S2508FOver := S2511Point
example : S2508ResidueScheme ⟶ S2504P1Over := S2511Point
example : S2511Point.left = S2511pointMap := rfl
example : S2511Point.left ≫ S2508FOver.hom = S2508ResidueScheme.hom := Over.w S2511Point
example : S2511pointMap ≫ S2508FOver.hom = S2508ResidueScheme.hom := S2511pointMap_structure

#print axioms S2511Point

end
