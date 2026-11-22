import tmp.sheaf.xif.paper.S2198GaloisMoveWitnessActual
import tmp.sheaf.xif.paper.S2046CyclotomicArtinActual
import Mathlib.NumberTheory.Cyclotomic.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2202NotInBaseActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual
open LeanFormal.IUT.XiFPaper.S2174CyclotomicWitnessActual
open LeanFormal.IUT.XiFPaper.S2184GaloisMoveActual
open LeanFormal.IUT.XiFPaper.S2163IntegralClosureNontrivialActual
open LeanFormal.IUT.XiFPaper.S2198GaloisMoveWitnessActual
open LeanFormal.IUT.XiFPaper.S2046CyclotomicArtinActual
open Polynomial

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The rational prime under the paper K-place. -/
noncomputable def s2202p : Nat :=
  (completionRationalPrime (sectionKPlace T b)).val

theorem s2202p_prime : Nat.Prime (s2202p T b) :=
  (completionRationalPrime (sectionKPlace T b)).property

/-- The Q_p-degree of the base completion. -/
noncomputable def s2202D : Nat :=
  Module.finrank (PadicScalarField (sectionKPlace T b))
    (NormalizedCompletion (sectionKPlace T b))

theorem s2202_pow_mul_pred_gt (d : Nat) :
    d < (s2202p T b) ^ d * ((s2202p T b) - 1) := by
  have hp : Nat.Prime (s2202p T b) := s2202p_prime T b
  have hp2 : 2 ≤ s2202p T b := hp.two_le
  have hd : d < 2 ^ d := Nat.lt_two_pow_self (n := d)
  have hle : 2 ^ d ≤ (s2202p T b) ^ d := Nat.pow_le_pow_left hp2 d
  have hpred : 1 ≤ (s2202p T b) - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hprod : 2 ^ d ≤ (s2202p T b) ^ d * ((s2202p T b) - 1) :=
    calc 2 ^ d ≤ (s2202p T b) ^ d := hle
      _ = (s2202p T b) ^ d * 1 := (mul_one _).symm
      _ ≤ (s2202p T b) ^ d * ((s2202p T b) - 1) := Nat.mul_le_mul_left _ hpred
  omega

theorem s2202_primitiveRoot_notInBase :
    S2184PrimitiveRootNotInBaseRequired T b
      ((s2202p T b) ^ (s2202D T b + 1))
      (pow_pos (Nat.Prime.pos (s2202p_prime T b)) _) := by
  intro hmem
  obtain ⟨x, hx⟩ := hmem
  letI := padicCompletionAlgebra (sectionKPlace T b)
  haveI : IsScalarTower (PadicScalarField (sectionKPlace T b))
      (NormalizedCompletion (sectionKPlace T b))
      (S2147PaperIntegralClosure T b) :=
    sourceAlgebraicClosureScalarTower (sectionKPlace T b)
  haveI : Fact (Nat.Prime (s2202p T b)) := ⟨s2202p_prime T b⟩
  haveI : NeZero ((s2202p T b) ^ (s2202D T b + 1)) :=
    ⟨pow_ne_zero _ (Nat.Prime.ne_zero (s2202p_prime T b))⟩
  let ζ : S2147PaperIntegralClosure T b :=
    s2174PrimitiveRoot T b ((s2202p T b) ^ (s2202D T b + 1))
      (pow_pos (Nat.Prime.pos (s2202p_prime T b)) _)
  have hζ : IsPrimitiveRoot ζ ((s2202p T b) ^ (s2202D T b + 1)) :=
    s2174PrimitiveRoot_spec T b ((s2202p T b) ^ (s2202D T b + 1))
      (pow_pos (Nat.Prime.pos (s2202p_prime T b)) _)
  have hcyc : cyclotomic ((s2202p T b) ^ (s2202D T b + 1))
      (PadicScalarField (sectionKPlace T b)) =
      minpoly (PadicScalarField (sectionKPlace T b)) ζ :=
    hζ.minpoly_eq_cyclotomic_of_irreducible
      (irreducible_cyclotomic_prime_pow_padic (s2202p T b) (s2202D T b))
  have hdegζ : (minpoly (PadicScalarField (sectionKPlace T b)) ζ).natDegree =
      (s2202p T b) ^ (s2202D T b) * ((s2202p T b) - 1) := by
    rw [← hcyc, natDegree_cyclotomic]
    exact Nat.totient_prime_pow (s2202p_prime T b) (Nat.succ_pos (s2202D T b))
  have hminx : minpoly (PadicScalarField (sectionKPlace T b)) ζ =
      minpoly (PadicScalarField (sectionKPlace T b)) x := by
    change minpoly (PadicScalarField (sectionKPlace T b))
      (s2174PrimitiveRoot T b ((s2202p T b) ^ (s2202D T b + 1))
        (pow_pos (Nat.Prime.pos (s2202p_prime T b)) _)) =
      minpoly (PadicScalarField (sectionKPlace T b)) x
    rw [← hx]
    exact minpoly.algebraMap_eq
      (algebraMap (NormalizedCompletion (sectionKPlace T b))
        (S2147PaperIntegralClosure T b)).injective x
  have hle : (minpoly (PadicScalarField (sectionKPlace T b)) x).natDegree ≤
      s2202D T b :=
    minpoly.natDegree_le x
  have hgt := s2202_pow_mul_pred_gt T b (s2202D T b)
  have hdegx : (minpoly (PadicScalarField (sectionKPlace T b)) x).natDegree =
      (s2202p T b) ^ (s2202D T b) * ((s2202p T b) - 1) := by
    rw [← hminx, hdegζ]
  omega

/-- The actual not-in-base datum required by S2198. -/
noncomputable def s2202NotInBase : S2198NotInBaseRequired T b where
  n := (s2202p T b) ^ (s2202D T b + 1)
  hn := pow_pos (Nat.Prime.pos (s2202p_prime T b)) _
  notInBase := s2202_primitiveRoot_notInBase T b

/-- The S2174 Galois move is now actual. -/
theorem s2202GaloisMovesPrimitiveRootRequired :
    S2174GaloisMovesPrimitiveRootRequired T b :=
  s2198GaloisMovesPrimitiveRootRequired_of_notInBase T b (s2202NotInBase T b)

/-- The S2147 nontrivial integral-closure action is now actual. -/
theorem s2202NontrivialAction :
    S2147IntegralClosureNontrivialActionRequired T b := by
  obtain ⟨n, hn, ⟨M⟩⟩ := s2202GaloisMovesPrimitiveRootRequired T b
  exact s2163NontrivialAction_of_witness T b
    (s2174CyclotomicWitnessOfGaloisMove T b n hn M)

/-- The exact S2163 cyclotomic witness now exists. -/
theorem s2202CyclotomicWitnessExists :
    S2163CyclotomicNontrivialWitnessRequired T b := by
  obtain ⟨n, hn, ⟨M⟩⟩ := s2202GaloisMovesPrimitiveRootRequired T b
  exact ⟨s2174CyclotomicWitnessOfGaloisMove T b n hn M⟩

#check s2202_pow_mul_pred_gt
#check s2202CyclotomicWitnessExists
#check s2202NotInBase
#check s2202GaloisMovesPrimitiveRootRequired
#check s2202NontrivialAction
#check s2202_primitiveRoot_notInBase

end LeanFormal.IUT.XiFPaper.S2202NotInBaseActual
end
