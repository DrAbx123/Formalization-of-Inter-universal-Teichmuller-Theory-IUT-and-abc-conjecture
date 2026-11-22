import tmp.sheaf.xif.paper.S2906CorrectedClauseABCD
import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual
import tmp.sheaf.xif.paper.S2907bClauseDEActual
import tmp.sheaf.xif.paper.S2907ClauseECorrected
import tmp.sheaf.xif.paper.S2907ClauseFCorrected
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import tmp.sheaf.xif.paper.S2846A6ClauseBFAssembly
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2906CorrectedClauseABCD
open LeanFormal.IUT.XiFPaper.S2907bClauseDEActual
open LeanFormal.IUT.XiFPaper.S2907ClauseECorrected
open LeanFormal.IUT.XiFPaper.S2907ClauseFCorrected
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2846A6ClauseBFAssembly
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.XiFPaper.S3104ClausesCtoF

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- Actual F6 rank-two 5-torsion basis, restated at S2847A6.curve. -/
noncomputable def S3104Basis :
    (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      S2847A6.curve.LTorsion S2771FiveLabel := by
  change (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      S2847Curve.LTorsion S2771FiveLabel
  exact S2847Basis

/-- Actual kernel-field identification at the restated basis. -/
noncomputable def S3104KernelIdentification :
    S2847A6.K ≃ₐ[S2847A6.F]
      (S2847A6.curve).galoisLTorsionKernelField S2771FiveLabel S3104Basis := by
  change S2847A6.K ≃ₐ[S2847A6.F]
      (S2847A6.curve).galoisLTorsionKernelField S2771FiveLabel S2847Basis
  exact S2846A6KernelIdentification

theorem S3104KernelIdentification_range :
    (Set.range fun x => (S3104KernelIdentification x :
      AlgebraicClosure S2847A6.F)) =
      ((S2847A6.curve).galoisLTorsionKernelField S2771FiveLabel S3104Basis :
        Set (AlgebraicClosure S2847A6.F)) := by
  change (Set.range fun x => (S2846A6KernelIdentification x :
      AlgebraicClosure S2847A6.F)) =
      ((S2847A6.curve).galoisLTorsionKernelField S2771FiveLabel S2847Basis :
        Set (AlgebraicClosure S2847A6.F))
  exact S2846A6KernelIdentification_range

/-- S3104 ClauseC: corrected clause structure with actual F6 torsion data
and actual kernel-field identification. The only non-data input is Serre
large image; S/C/B are the corrected source record and its ClauseA/B. -/
noncomputable def S3104ClauseCCorrected
    (S : SourceSignQuotientDataCorrected (A := S2847A6))
    (C : S2906ClauseACorrected (A := S2847A6) S)
    (B : S2906ClauseBCorrected (A := S2847A6) S C)
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod S2771FiveLabel.value))) ≤
        (S2847A6.curve.galoisLTorsionMatrixRepresentation S2771FiveLabel S3104Basis).range) :
    S2906ClauseCCorrected (A := S2847A6) S C B where
  torsion23_rational := S2847_torsion23
  torsion_basis := S3104Basis
  representation := S2847A6.curve.galoisLTorsionMatrixRepresentation S2771FiveLabel S3104Basis
  representation_eq_canonical := rfl
  image_contains_SL2 := imageContainsSL2
  kernel_field_identification := S3104KernelIdentification
  kernel_field_identification_range := S3104KernelIdentification_range

/-- S3104 ClauseD explicit missing inputs: exactly the K-side witnesses of
S2907ClauseDScaffold. -/
structure S3104ClauseDInputs
    (S : SourceSignQuotientDataCorrected (A := S2847A6))
    (C : S2906ClauseACorrected (A := S2847A6) S)
    (B : S2906ClauseBCorrected (A := S2847A6) S C)
    (D : S2906ClauseCCorrected (A := S2847A6) S C B) where
  kSignAction : Iut.OrbicurveSignAction S.xK
  kQuotient : Iut.OrbicurveSignInvariantMorphism kSignAction S.cK
  kQuotientWitness : Iut.OrbicurveSignQuotientWitness kSignAction kQuotient
  kQuotientExtension : SourceOrbicurveMorphismScalarExtension
    S.xKExtension S.cKExtension S.quotient.map
  kQuotientMapEqExtension : kQuotient.map = Iut.HyperbolicOrbicurve.Hom.cast
    S.xK_eq_extension.symm S.cK_eq_extension.symm kQuotientExtension.result
  kTorsionCover : SourceOrbicurveFiniteEtaleCover S.xK S.cK
  kTorsionCoverMapEqQuotient : kTorsionCover.map = kQuotient.map
  xGroups : SourceOrbicurveGroupData S.xK
    (Iut.AbsoluteGaloisProfinite S2847A6.K)
  cGroups : SourceOrbicurveGroupData S.cK
    (Iut.AbsoluteGaloisProfinite S2847A6.K)
  groupInclusion :
    Iut.ProfiniteFundamentalGroupInclusion
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite S2847A6.K)
      xGroups.sequence cGroups.sequence
  xToFGroups :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite S2847A6.K)
      S.xFGroups.sequence.geometric S.xFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite S2847A6.F)
      xGroups.sequence S.xFGroups.sequence
  cToFGroups :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite S2847A6.K)
      S.cFGroups.sequence.geometric S.cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite S2847A6.F)
      cGroups.sequence S.cFGroups.sequence

/-- ClauseD from the explicit K-side input package. -/
noncomputable def S3104ClauseDCorrected
    (S : SourceSignQuotientDataCorrected (A := S2847A6))
    (C : S2906ClauseACorrected (A := S2847A6) S)
    (B : S2906ClauseBCorrected (A := S2847A6) S C)
    (D : S2906ClauseCCorrected (A := S2847A6) S C B)
    (I : S3104ClauseDInputs S C B D) :
    S2906ClauseDCorrected (A := S2847A6) S C B D where
  k_signAction := I.kSignAction
  k_quotient := I.kQuotient
  k_quotientWitness := I.kQuotientWitness
  k_quotientExtension := I.kQuotientExtension
  k_quotient_map_eq_extension := I.kQuotientMapEqExtension
  k_l_torsion_cover := I.kTorsionCover
  k_l_torsion_cover_map_eq_quotient := I.kTorsionCoverMapEqQuotient
  x_groups := I.xGroups
  c_groups := I.cGroups
  group_inclusion := I.groupInclusion
  x_to_F_groups := I.xToFGroups
  c_to_F_groups := I.cToFGroups

/-- S3104 ClauseE explicit missing inputs: the local families. -/
structure S3104ClauseEInputs
    (S : SourceSignQuotientDataCorrected (A := S2847A6))
    (C : S2906ClauseACorrected (A := S2847A6) S)
    (B : S2906ClauseBCorrected (A := S2847A6) S C)
    (D : S2906ClauseCCorrected (A := S2847A6) S C B)
    (E : S2906ClauseDCorrected (A := S2847A6) S C B D) where
  finiteLocal : ∀ (v : {v : NumberFieldPlace S2847A6.K // v ∈ S.V})
    (hv : v.1.IsFinite),
    S2907FiniteLocalSourceCorrected S C B D E (selectedFinitePlace hv)
  infiniteLocal : ∀ (v : {v : NumberFieldPlace S2847A6.K // v ∈ S.V})
    (hv : v.1.IsInfinite),
    S2907InfiniteLocalSourceCorrected S C B D E (selectedInfinitePlace hv)

/-- ClauseE from S.V data and explicit local families. -/
noncomputable def S3104ClauseECorrected
    (S : SourceSignQuotientDataCorrected (A := S2847A6))
    (C : S2906ClauseACorrected (A := S2847A6) S)
    (B : S2906ClauseBCorrected (A := S2847A6) S C)
    (D : S2906ClauseCCorrected (A := S2847A6) S C B)
    (E : S2906ClauseDCorrected (A := S2847A6) S C B D)
    (I : S3104ClauseEInputs S C B D E) :
    S2907ClauseEScaffold S C B D E where
  selected_eq_V := S.V_eq_section
  selected_equiv := S.V_mod_bijection
  finite_local := I.finiteLocal
  infinite_local := I.infiniteLocal

/-- S3104 ClauseF explicit missing inputs: exactly the canonical-boundary data
of SourceClauseF.ofCanonicalBoundaryData, at the corrected K-quotient. -/
structure S3104ClauseFInputs
    (S : SourceSignQuotientDataCorrected (A := S2847A6))
    (C : S2906ClauseACorrected (A := S2847A6) S)
    (B : S2906ClauseBCorrected (A := S2847A6) S C)
    (D : S2906ClauseCCorrected (A := S2847A6) S C B)
    (E : S2906ClauseDCorrected (A := S2847A6) S C B D) where
  originMap :
    {q : (S2907CanonicalKQuotientData S C B D).Quotient // q ≠ 0} →
      Iut.OrbicurveBoundaryCusp S.cK
  originMap_epsilon :
    originMap
      ⟨(S2907CanonicalKQuotientData S C B D).distinguishedClass,
        (S2907CanonicalKQuotientData S C B D).distinguishedClass_nonzero⟩ =
      S.epsilon
  cuspDecomposition : Iut.OrbicurveCuspidalDecompositionData E.c_groups.groups
  cuspDecomposition_origin :
    cuspDecomposition.cusp =
      (S2907BoundaryOrigin S C B D originMap originMap_epsilon).cusp

/-- ClauseF scaffold from the explicit origin/cusp input package. -/
noncomputable def S3104ClauseFScaffold
    (S : SourceSignQuotientDataCorrected (A := S2847A6))
    (C : S2906ClauseACorrected (A := S2847A6) S)
    (B : S2906ClauseBCorrected (A := S2847A6) S C)
    (D : S2906ClauseCCorrected (A := S2847A6) S C B)
    (E : S2906ClauseDCorrected (A := S2847A6) S C B D)
    (I : S3104ClauseFInputs S C B D E) :
    S2907ClauseFScaffold S C B D E where
  originMap := I.originMap
  originMap_epsilon := I.originMap_epsilon
  cuspDecomposition := I.cuspDecomposition
  cuspDecomposition_origin := I.cuspDecomposition_origin

#check S3104Basis
#check S3104ClauseCCorrected
#check S3104ClauseDCorrected
#check S3104ClauseECorrected
#check S3104ClauseFScaffold
#print axioms S3104Basis
#print axioms S3104ClauseCCorrected
#print axioms S3104ClauseDCorrected
#print axioms S3104ClauseECorrected
#print axioms S3104ClauseFScaffold

/-- Single explicit input package for ClauseD/E/F. Every field is a missing
K-side/local/cusp input; none is fabricated. -/
structure S3104ClauseDEFInputs
    (S : SourceSignQuotientDataCorrected (A := S2847A6))
    (C : S2906ClauseACorrected (A := S2847A6) S)
    (B : S2906ClauseBCorrected (A := S2847A6) S C)
    (D : S2906ClauseCCorrected (A := S2847A6) S C B) where
  d : S3104ClauseDInputs S C B D
  e : S3104ClauseEInputs S C B D
    (S3104ClauseDCorrected S C B D d)
  f : S3104ClauseFInputs S C B D
    (S3104ClauseDCorrected S C B D d)

/-- ClauseD from the combined package. -/
noncomputable def S3104ClauseD_of_DEFInputs
    (S : SourceSignQuotientDataCorrected (A := S2847A6))
    (C : S2906ClauseACorrected (A := S2847A6) S)
    (B : S2906ClauseBCorrected (A := S2847A6) S C)
    (D : S2906ClauseCCorrected (A := S2847A6) S C B)
    (I : S3104ClauseDEFInputs S C B D) :
    S2906ClauseDCorrected (A := S2847A6) S C B D :=
  S3104ClauseDCorrected S C B D I.d

/-- ClauseE from the combined package. -/
noncomputable def S3104ClauseE_of_DEFInputs
    (S : SourceSignQuotientDataCorrected (A := S2847A6))
    (C : S2906ClauseACorrected (A := S2847A6) S)
    (B : S2906ClauseBCorrected (A := S2847A6) S C)
    (D : S2906ClauseCCorrected (A := S2847A6) S C B)
    (I : S3104ClauseDEFInputs S C B D) :
    S2907ClauseEScaffold S C B D
      (S3104ClauseD_of_DEFInputs S C B D I) :=
  S3104ClauseECorrected S C B D
    (S3104ClauseD_of_DEFInputs S C B D I) I.e

/-- ClauseF scaffold from the combined package. -/
noncomputable def S3104ClauseF_of_DEFInputs
    (S : SourceSignQuotientDataCorrected (A := S2847A6))
    (C : S2906ClauseACorrected (A := S2847A6) S)
    (B : S2906ClauseBCorrected (A := S2847A6) S C)
    (D : S2906ClauseCCorrected (A := S2847A6) S C B)
    (I : S3104ClauseDEFInputs S C B D) :
    S2907ClauseFScaffold S C B D
      (S3104ClauseD_of_DEFInputs S C B D I) :=
  S3104ClauseFScaffold S C B D
    (S3104ClauseD_of_DEFInputs S C B D I) I.f

#check S3104ClauseDEFInputs
#check S3104ClauseD_of_DEFInputs
#check S3104ClauseE_of_DEFInputs
#check S3104ClauseF_of_DEFInputs
#print axioms S3104ClauseDEFInputs
#print axioms S3104ClauseF_of_DEFInputs

end LeanFormal.IUT.XiFPaper.S3104ClausesCtoF
end