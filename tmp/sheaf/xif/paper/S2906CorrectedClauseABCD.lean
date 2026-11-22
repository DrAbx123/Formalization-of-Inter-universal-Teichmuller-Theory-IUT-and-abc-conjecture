import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2906CorrectedClauseABCD

universe u

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}

/-- Corrected ClauseA: same fields as SourceClauseA, parameterized by the
corrected sign-quotient record. -/
structure S2906ClauseACorrected (S : SourceSignQuotientDataCorrected A) where
  stable_reduction_nonarchimedean :
    ∀ p : NumberField.FinitePlace A.F, A.curve.HasStableReductionAt p
  field_of_moduli : SourceFieldOfModuli A
  maximal_solvable_extension : IntermediateField A.Fmod A.F
  maximal_solvable_property :
    isFiniteSolvableGaloisSubextension maximal_solvable_extension
  maximal_solvable_contains :
    ∀ E : IntermediateField A.Fmod A.F,
      isFiniteSolvableGaloisSubextension E → E ≤ maximal_solvable_extension

/-- Corrected ClauseB: same fields as SourceClauseB, with S.V_mod_bad read from
the corrected record. -/
structure S2906ClauseBCorrected
    (S : SourceSignQuotientDataCorrected A)
    (C : S2906ClauseACorrected S) where
  multiplicative_over_bad :
    ∀ p : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad →
      A.curve.HasMultiplicativeReductionAt p
  q_comparison :
    ∀ (p : NumberField.FinitePlace A.F)
      (_hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad),
      Nonempty (SourceTateComparisonWitness A p)
  residue_characteristic_prime_to_l :
    ∀ (p : NumberField.FinitePlace A.F)
      (_hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad),
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := A.Fmod) p))

/-- Corrected ClauseC: same fields as SourceClauseC. -/
structure S2906ClauseCCorrected
    (S : SourceSignQuotientDataCorrected A)
    (C : S2906ClauseACorrected S)
    (B : S2906ClauseBCorrected S C) where
  torsion23_rational : PuncturedEllipticCurve.Torsion23Rational A.curve
  torsion_basis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l
  representation :
    (SourceAbsoluteGalois A) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)
  representation_eq_canonical :
    representation = A.curve.galoisLTorsionMatrixRepresentation l torsion_basis
  image_contains_SL2 :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      representation.range
  kernel_field_identification :
    A.K ≃ₐ[A.F] A.curve.galoisLTorsionKernelField l torsion_basis
  kernel_field_identification_range :
    Set.range (fun x : A.K =>
      (kernel_field_identification x : AlgebraicClosure A.F)) =
      (A.curve.galoisLTorsionKernelField l torsion_basis :
        Set (AlgebraicClosure A.F))

/-- Corrected ClauseD: same 11 K-side/group fields, with all S projections read
from the corrected record. -/
structure S2906ClauseDCorrected
    (S : SourceSignQuotientDataCorrected A)
    (C : S2906ClauseACorrected S)
    (B : S2906ClauseBCorrected S C)
    (D : S2906ClauseCCorrected S C B) where
  k_signAction : Iut.OrbicurveSignAction S.xK
  k_quotient : Iut.OrbicurveSignInvariantMorphism k_signAction S.cK
  k_quotientWitness : Iut.OrbicurveSignQuotientWitness k_signAction k_quotient
  k_quotientExtension : SourceOrbicurveMorphismScalarExtension
    S.xKExtension S.cKExtension S.quotient.map
  k_quotient_map_eq_extension :
    k_quotient.map = Iut.HyperbolicOrbicurve.Hom.cast
      S.xK_eq_extension.symm S.cK_eq_extension.symm
      k_quotientExtension.result
  k_l_torsion_cover : SourceOrbicurveFiniteEtaleCover S.xK S.cK
  k_l_torsion_cover_map_eq_quotient :
    k_l_torsion_cover.map = k_quotient.map
  x_groups : SourceOrbicurveGroupData S.xK (Iut.AbsoluteGaloisProfinite A.K)
  c_groups : SourceOrbicurveGroupData S.cK (Iut.AbsoluteGaloisProfinite A.K)
  group_inclusion :
    Iut.ProfiniteFundamentalGroupInclusion
      x_groups.sequence.geometric x_groups.sequence.arithmetic
      c_groups.sequence.geometric c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      x_groups.sequence c_groups.sequence
  x_to_F_groups :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      x_groups.sequence.geometric x_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      S.xFGroups.sequence.geometric S.xFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.F)
      x_groups.sequence S.xFGroups.sequence
  c_to_F_groups :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      c_groups.sequence.geometric c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      S.cFGroups.sequence.geometric S.cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.F)
      c_groups.sequence S.cFGroups.sequence

#check S2906ClauseACorrected
#check S2906ClauseBCorrected
#check S2906ClauseCCorrected
#check S2906ClauseDCorrected

end LeanFormal.IUT.XiFPaper.S2906CorrectedClauseABCD
end
