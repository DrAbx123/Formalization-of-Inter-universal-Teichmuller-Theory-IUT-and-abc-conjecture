import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2689SourceBadQAbsLogActual
import tmp.sheaf.xif.paper.S2699GenericQPilotRayActual
import tmp.sheaf.xif.paper.S2702FourPlaceDataActual
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2689SourceBadQAbsLogActual
open LeanFormal.IUT.XiFPaper.S2699GenericQPilotRayActual
open LeanFormal.IUT.XiFPaper.S2702FourPlaceDataActual
local instance s2701GI : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
noncomputable def qq (l : PrimeGeFive) (D : S2696FourPlaceData) :
    (p : NumberField.FinitePlace GaussianField) → p ∈ S2696Vbad D → Real :=
  fun p hp => |Real.log (badPlaceQProxy (S2696Selection l D) ⟨p, hp⟩)|
#check S2702FourPlaceData

#check (S2702Place5a_residueCharacteristic)
#check (S2702Place2161b_residueCharacteristic)
end
