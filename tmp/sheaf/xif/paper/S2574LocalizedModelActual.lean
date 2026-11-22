import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2532LocalizedAbstractActual
import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

noncomputable section
open Polynomial
open scoped Polynomial

namespace LeanFormal.IUT.XiFPaper.S2574LocalizedModelActual

open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- The leading coefficient of S2132Psi5Z. -/
def Lc : ℤ := 343597383680

lemma Lc_eq : Lc = 2 ^ 36 * 5 := by decide

/-- The localized base ring O_F'[1/(2^36*5)]. -/
abbrev R : Type := Localization.Away (algebraMap ℤ (NumberField.RingOfIntegers S1720Field) Lc)

/-- The monic scalar normalization of the integer model over R. -/
def f : R[X] :=
  C (IsLocalization.Away.invSelf (algebraMap ℤ (NumberField.RingOfIntegers S1720Field) Lc)) *
    S2132Psi5Z.map (algebraMap ℤ R)

lemma f_coeff_12 : f.coeff 12 = 1 := by
  unfold f
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
  have hcoeff : S2132Psi5Z.coeff 12 = Lc := by
    unfold S2132Psi5Z Lc
    simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_pow]
  rw [hcoeff]
  change IsLocalization.Away.invSelf (algebraMap ℤ (NumberField.RingOfIntegers S1720Field) Lc) *
      algebraMap (NumberField.RingOfIntegers S1720Field) R
        (algebraMap ℤ (NumberField.RingOfIntegers S1720Field) Lc) = 1
  rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.RingOfIntegers S1720Field) R]
  rw [mul_comm]
  exact IsLocalization.Away.mul_invSelf (S := R) (x := algebraMap ℤ (NumberField.RingOfIntegers S1720Field) Lc)

lemma f_natDegree_le : f.natDegree ≤ 12 := by
  unfold f
  calc (C (IsLocalization.Away.invSelf (algebraMap ℤ (NumberField.RingOfIntegers S1720Field) Lc)) *
        S2132Psi5Z.map (algebraMap ℤ R)).natDegree
      ≤ (S2132Psi5Z.map (algebraMap ℤ R)).natDegree :=
        natDegree_C_mul_le _ _
    _ ≤ S2132Psi5Z.natDegree := Polynomial.natDegree_map_le
    _ ≤ 12 := by unfold S2132Psi5Z; compute_degree!

lemma f_natDegree : f.natDegree = 12 := by
  have hLc : Lc ≠ 0 := by decide
  have hx : algebraMap ℤ (NumberField.RingOfIntegers S1720Field) Lc ≠ 0 := by
    intro h
    have hinj : Function.Injective (algebraMap ℤ (NumberField.RingOfIntegers S1720Field)) :=
      Int.cast_injective
    exact hLc (hinj (by simpa using h))
  have hM : Submonoid.powers (algebraMap ℤ (NumberField.RingOfIntegers S1720Field) Lc) ≤
      nonZeroDivisors (NumberField.RingOfIntegers S1720Field) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hx
  haveI : IsDomain R := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (algebraMap ℤ (NumberField.RingOfIntegers S1720Field) Lc)) (S := R) hM
  apply natDegree_eq_of_le_of_coeff_ne_zero f_natDegree_le
  rw [f_coeff_12]
  exact one_ne_zero

theorem f_monic : f.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, f_natDegree, f_coeff_12]



/-! ## The localized residue-data design and its connection to S2470 -/

/-- Localized residue data over R = O_F'[1/(2^36*5)] with the monic model f. -/
structure S2574LocalizedResidueData where
  p : Ideal R
  p_max : p.IsMaximal
  fbar_irreducible : Irreducible (f.map (Ideal.Quotient.mk p))
  fbar_degree : (f.map (Ideal.Quotient.mk p)).natDegree = 12

/-- The exact remaining arithmetic transport: localized residue data produce the
actual twelve-cycle in the mod-5 Galois range. -/
def S2574LocalizedDedekindToTwelveCycle : Prop :=
  ∀ _D : S2574LocalizedResidueData,
    LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual.S2440TwelveCycleInputRequired

/-- Connection scheme: localized residue data + transport imply the S2470 target. -/
theorem S2574Target_of_localized
    (D : S2574LocalizedResidueData)
    (htrans : S2574LocalizedDedekindToTwelveCycle) :
    LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual.S2470Target :=
  LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual.S2470Target_of_twelveCycle (htrans D)

end LeanFormal.IUT.XiFPaper.S2574LocalizedModelActual
end