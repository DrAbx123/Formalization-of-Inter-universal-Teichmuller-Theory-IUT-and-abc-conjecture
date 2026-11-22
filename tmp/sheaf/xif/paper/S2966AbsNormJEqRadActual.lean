import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.S2796SupportAbsNormLeRadSqActual
import tmp.sheaf.xif.paper.S2921HeightBridgeActual
import tmp.sheaf.xif.paper.S2743SupportIdealAbsNormLowerActual
import tmp.sheaf.xif.paper.S2749SupportEqualityActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2796SupportAbsNormLeRadSqActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2743SupportIdealAbsNormLowerActual
open LeanFormal.IUT.XiFPaper.S2749SupportEqualityActual
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2966AbsNormJEqRadActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- S2752J for the concrete five-label is exactly the Gaussian support ideal. -/
theorem S2966_J_eq_supportIdeal (a b c : Nat) :
    S2752J S2771FiveLabel a b c =
      supportIdeal (K := GaussianField) (abcRationalPoint a c) := rfl

/-- The absNorm is the Gaussian support-ideal absNorm. -/
theorem S2966_absNorm_eq_supportIdeal (a b c : Nat) :
    Ideal.absNorm (S2752J S2771FiveLabel a b c) =
      Ideal.absNorm (supportIdeal (K := GaussianField) (abcRationalPoint a c)) := by
  rfl

/-- Exact comparison, upper side: absNorm J is at most rad^2. -/
theorem S2966_absNorm_le_radSq (a b c : Nat) (habc : IsABCTriple a b c) :
    Ideal.absNorm (S2752J S2771FiveLabel a b c) <=
      (natRadical (a * b * c)) ^ 2 := by
  rw [S2966_absNorm_eq_supportIdeal]
  exact S2796_absNorm_supportIdeal_le_radSq habc

/-- Exact comparison, lower side: rad is at most absNorm J. -/
theorem S2966_rad_le_absNorm (a b c : Nat) (habc : IsABCTriple a b c) :
    natRadical (a * b * c) <=
      Ideal.absNorm (S2752J S2771FiveLabel a b c) := by
  have h1 : (Finset.prod (arithmeticPrimeSupport (abcRationalPoint a c))
      (fun p => p)) = natRadical (a * b * c) :=
    S2749_prod_support_eq_radical habc
  have h2 : (Finset.prod (arithmeticPrimeSupport (abcRationalPoint a c))
      (fun p => p)) =
      (Finset.univ.prod (fun i : SupportIndex (abcRationalPoint a c) => i.1)) := by
    simpa using (Finset.prod_attach
      (s := arithmeticPrimeSupport (abcRationalPoint a c))
      (f := fun p => p)).symm
  have h3 := S2743_prod_support_le_supportIdeal_absNorm
    (K := (S2735Arithmetic S2771FiveLabel).K) (abcRationalPoint a c)
  rw [← h1]
  simpa [S2752J, h2] using h3

/-- S2921S is exactly the log of absNorm J. -/
theorem S2966_S2921S_eq_log_absNorm (a b c : Nat) :
    S2921S a b c =
      Real.log ((Ideal.absNorm (S2752J S2771FiveLabel a b c) : Nat) : Real) := rfl

/-- Conditional exact equality: if absNorm J = rad, then S2921S = log rad. -/
theorem S2966_S2921S_eq_log_rad (a b c : Nat)
    (h : Ideal.absNorm (S2752J S2771FiveLabel a b c) =
      natRadical (a * b * c)) :
    S2921S a b c = Real.log ((natRadical (a * b * c) : Nat) : Real) := by
  rw [S2966_S2921S_eq_log_absNorm, h]

#check S2966_J_eq_supportIdeal
#check S2966_absNorm_eq_supportIdeal
#check S2966_absNorm_le_radSq
#check S2966_rad_le_absNorm
#check S2966_S2921S_eq_log_absNorm
#check S2966_S2921S_eq_log_rad
#print axioms S2966_rad_le_absNorm
#print axioms S2966_S2921S_eq_log_absNorm

end LeanFormal.IUT.XiFPaper.S2966AbsNormJEqRadActual
end