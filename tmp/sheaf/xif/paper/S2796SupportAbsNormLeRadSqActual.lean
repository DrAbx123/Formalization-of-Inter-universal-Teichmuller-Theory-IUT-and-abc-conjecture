import tmp.sheaf.xif.paper.S2795PlaceAbsNormLeSqActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import tmp.sheaf.xif.paper.S2739FinsetSupportActual
import tmp.sheaf.xif.paper.S2749SupportEqualityActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.XiFPaper.S2749SupportEqualityActual
open LeanFormal.IUT.XiFPaper.S2795PlaceAbsNormLeSqActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2796SupportAbsNormLeRadSqActual



theorem S2796_absNorm_supportIdeal_le_radSq
    {a b c : Nat} (habc : IsABCTriple a b c) :
    Ideal.absNorm (supportIdeal (K := GaussianField) (abcRationalPoint a c))
      <= (natRadical (a * b * c)) ^ 2 := by
  rw [supportIdeal_absNorm]
  have hprod : (∏ i : SupportIndex (abcRationalPoint a c), i.1)
      = (∏ p ∈ arithmeticPrimeSupport (abcRationalPoint a c), p) :=
    Finset.prod_coe_sort (arithmeticPrimeSupport (abcRationalPoint a c)) (fun p : Nat => p)

  calc
    (∏ i : SupportIndex (abcRationalPoint a c),
        Ideal.absNorm ((supportPlace (K := GaussianField) (abcRationalPoint a c) i).maximalIdeal.asIdeal))
        <= ∏ i : SupportIndex (abcRationalPoint a c), i.1 ^ 2 :=
          Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => S2795_place_absNorm_le_sq _ i)
    _ = (∏ i : SupportIndex (abcRationalPoint a c), i.1) ^ 2 := by
          rw [Finset.prod_pow]
    _ = (∏ p ∈ arithmeticPrimeSupport (abcRationalPoint a c), p) ^ 2 := by rw [hprod]
    _ = (natRadical (a * b * c)) ^ 2 := by
          rw [S2749_prod_support_eq_radical habc]

end LeanFormal.IUT.XiFPaper.S2796SupportAbsNormLeRadSqActual
end
