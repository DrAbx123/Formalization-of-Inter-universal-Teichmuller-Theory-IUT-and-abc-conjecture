import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import tmp.sheaf.xif.paper.S1667AdmissibleCurveActual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual
import tmp.sheaf.xif.paper.S2055DicksonClassActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.FieldTheory.Galois.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual

open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2055DicksonClassActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open Polynomial
open NumberField

/-- Actual Kummer--Dedekind reduction: for a number field `K`, an integral
generator `θ`, and a monic irreducible factor `Q` of `minpoly θ` modulo `p`
(with `p` not dividing the conductor exponent), the residual degree of the
corresponding prime is exactly `natDegree Q`. -/
theorem s2057InertiaDeg_eq_natDegree
    {K : Type*} [Field K] [NumberField K]
    {θ : NumberField.RingOfIntegers K} {p : ℕ} [Fact (Nat.Prime p)]
    (hp : ¬ p ∣ RingOfIntegers.exponent θ)
    {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod θ p) :
    (((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q, hQ⟩ : Ideal (𝓞 K)).inertiaDeg ℤ) = Q.natDegree :=
  NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ

/-- The actual odd 5-division polynomial of the S1720 curve over Q. -/
noncomputable def S2057Psi5Q : ℚ[X] :=
  S1667Curve.preΨ 5

/-- The same polynomial over F' = S1720Field. -/
noncomputable def S2057Psi5F : S1720Field[X] :=
  S2057Psi5Q.map (algebraMap ℚ S1720Field)

theorem S2057Psi5Q_separable : S2057Psi5Q.Separable := by
  unfold S2057Psi5Q
  letI : S1667Curve.IsElliptic := S1667Curve_isElliptic
  exact S1942_preΨ_five_separable S1667Curve

theorem S2057Psi5F_separable : S2057Psi5F.Separable := by
  unfold S2057Psi5F
  exact S2057Psi5Q_separable.map

/-- The actual splitting field over F' of the odd 5-division polynomial. -/
abbrev S2057FiveDivisionField : Type :=
  Polynomial.SplittingField S2057Psi5F

/-- The actual 5-division field over F' is finite Galois. -/
instance S2057FiveDivisionField_isGalois :
    IsGalois S1720Field S2057FiveDivisionField :=
  IsGalois.of_separable_splitting_field (p := S2057Psi5F) S2057Psi5F_separable

/-- Exact mod-29 factorization certificate: an integer model of psi5, its
reduction modulo 29, an irreducible quadratic factor and an irreducible
degree-10 factor with product equal to the reduction.  No inhabitant is
asserted. -/
structure S2057Mod29FactorizationData where
  integerModel : ℤ[X]
  integerModel_map : integerModel.map (Int.castRingHom ℚ) = S2057Psi5Q
  factor2 : (ZMod 29)[X]
  factor10 : (ZMod 29)[X]
  product_eq :
    factor2 * factor10 = integerModel.map (Int.castRingHom (ZMod 29))
  factor2_irreducible : Irreducible factor2
  factor10_irreducible : Irreducible factor10
  factor2_degree : factor2.natDegree = 2
  factor10_degree : factor10.natDegree = 10

/-- Exact Frob_p cycle-type bridge target: an actual Frobenius conjugacy
element of Gal(F'/Q) whose permutation of the twelve pairs has cycle type
(10,2), together with the factorization data identifying its cycle type with
the mod-29 factor degrees.  No inhabitant is asserted. -/
structure S2057FrobMod29CycleTypeBridge where
  factorization : S2057Mod29FactorizationData
  frobenius : S1720Field ≃ₐ[ℚ] S1720Field
  permutation : Equiv.Perm S2056Pair
  cycleType_eq : permutation.cycleType = ({2, 10} : Multiset ℕ)

/-- Exact range-hypothesis data at a fixed actual basis, used by the final
assembly.  The three fields are exactly the hypotheses of
s2041RangeTop_of_rangeHypotheses. -/
structure S2057RangeHypothesesData
    (b : S1725TorsionBasis S1987Five) where
  det_surjective : DetSurjectiveOn
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range
  pair_transitive : PairTransitive
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range
  cycle_type_102 : HasCycleType102
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range

/-- Final assembly: exact range-hypothesis data gives the S1987 D5
large-image target. -/
theorem s2057Target_of_rangeHypotheses
    (b : S1725TorsionBasis S1987Five)
    (D : S2057RangeHypothesesData b) :
    S1987D5LargeImageFive :=
  S1987D5LargeImageFive_of_fullRange b (by
    exact S2055LargeImage_of_dickson _ D.det_surjective D.pair_transitive
      D.cycle_type_102)

end LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual

end
