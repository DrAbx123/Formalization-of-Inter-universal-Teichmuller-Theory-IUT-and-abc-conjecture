import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2689SourceBadQAbsLogActual
import tmp.sheaf.xif.paper.S2703FourPlaceDataActual
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2689SourceBadQAbsLogActual
open LeanFormal.IUT.XiFPaper.S2703FourPlaceDataActual
local instance s2701GI : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
#check Finset.sum_pair
#check Finset.sum_le_sum_of_subset_of_nonneg
#check Finset.sum_le_sum_of_subset
#check Finset.single_le_sum
#check S2703FourPlaceData
#check S2699ResidueCharacteristicPlus
#check S2698ResidueCharacteristicPlus
#check S2703FourPlaceData_residue5a
end
