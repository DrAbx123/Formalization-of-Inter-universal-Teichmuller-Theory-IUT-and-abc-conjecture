import tmp.sheaf.xif.paper.S3132RootedScalingDataFormulaActual
import tmp.sheaf.xif.paper.S3132ThetaSideSharpResidualReducedActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3132VFormScalingReductionActual
open LeanFormal.IUT.XiFPaper.S3132RootedScalingDataTrivialActual
open LeanFormal.IUT.XiFPaper.S3132RootedScalingDataFormulaActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceNormalizationClosureActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelClauseResidualActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideSharpResidualReducedActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual

namespace LeanFormal.IUT.XiFPaper.Hull05WeightedIdentityActual

/-!
# STEP 0 prior-art: weighted rooted identity|rootHalfCoefficient|RootedScalingDecomposition|ReducedVFormResidual -> hits S3132VFormScalingReductionActual (ReducedVFormResidual/vformCanonical_of_reducedResidual), S3132RootedScalingDataFormulaActual (formula scalars; paper-gap reuse), S3132ThetaSideSharpResidualReducedActual (sharp residual = R2), BadPlacePaperRootThetaHullActual:56/68 -> REUSE; this file gives the H2 concrete weighted identity COMPLETE-PROOF ROW with rootHalfCoefficient.

# [Hull] 05: H2 concrete weighted rooted identity (rootHalfCoefficient) - complete proof row

H2 (R2) is the weighted rooted identity
  sourceVFormLogVolume = sum_b nativeBadLocalWeight b * rootThetaHullLog_b
with rootThetaHullLog_b at the paper-faithful coefficient rootHalfCoefficient b.
COMPLETE proof chain (every step a proved tree theorem):
  (i) coefficient identification hc: rootHalfCoefficient = paperRootCoefficientFamily;
  (ii) per-place paper-hull formula gap G: PaperRootHullFormulaGap;
  (iii) one scalar-match equation hmatch.
From these we derive RootedScalingDecomposition (reused formula theorem), then
ReducedVFormResidual, then sourceVForm = canonical rooted readout
(vformCanonical_of_reducedResidual), then ModelWeightedRootedIdentity
(sharp residual = R2).  The three inputs are the named residuals; no closure beyond
the conditional row.  Registry frozen 14041.
-/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- The concrete Haar family used by the formula chain (definitionally the
stage4 lgpNativeHaarFamily family). -/
noncomputable def hull05Mu :
    (b : Bad (nativePlaceSelection (lgpModelNativeData M))) →
      Measure (qVFamTensorBlock (lgpModelNativeData M) b) :=
  fun b => Measure.addHaar

local instance hull05Mu_isAddHaar :
    ∀ b : Bad (nativePlaceSelection (lgpModelNativeData M)),
      Measure.IsAddHaarMeasure (hull05Mu M b) :=
  fun b => by unfold hull05Mu; infer_instance

/-- **The concrete weighted rooted sum** (explicit rootHalfCoefficient form). -/
noncomputable def hull05WeightedSum : ℝ :=
  ∑ b : Bad (nativePlaceSelection (lgpModelNativeData M)),
    nativeBadLocalWeight (lgpModelNativeData M) b *
      rootThetaHullLog (l := l)
        (qVFamTensorPlaces (lgpModelNativeData M) b) qVFamTensorTuple
        (hull05Mu M b)
        (rootHalfCoefficient (l := l) (lgpModelNativeData M) b)

/-- **H2 from the explicit scaling data:** (R1) rooted scaling decomposition plus
the scalar-match equation gives the concrete weighted rooted identity (no eta/
instance detour: the sum of log-scalars is rewritten to the rooted sum). -/
theorem hull05_weightedIdentity_of_scaling
    (hR1 : RootedScalingDecomposition (T := lgpModelNativeData M)
      (fun b => lgpNativeHaarFamily (lgpModelNativeData M) b)
      (paperFormulaScalar (lgpModelNativeData M)))
    (hmatch : sourceVFormLogVolume =
      ∑ b : Bad (nativePlaceSelection (lgpModelNativeData M)),
        nativeBadLocalWeight (lgpModelNativeData M) b *
          Real.log (paperFormulaScalar (lgpModelNativeData M) b)) :
    ModelWeightedRootedIdentity M := by
  show sourceVFormLogVolume =
    ∑ b : Bad (nativePlaceSelection (lgpModelNativeData M)),
      nativeBadLocalWeight (lgpModelNativeData M) b *
        rootThetaHullLog (l := l)
          (qVFamTensorPlaces (lgpModelNativeData M) b) qVFamTensorTuple
          (lgpNativeHaarFamily (lgpModelNativeData M) b)
          (rootHalfCoefficient (l := l) (lgpModelNativeData M) b)
  rw [hmatch]
  apply Finset.sum_congr rfl
  intro b _
  rw [hR1 b]

/-- **H2 COMPLETE-PROOF ROW.** From the three named inputs (hc, paper-hull formula
gap, scalar match) the concrete weighted rooted identity holds. -/
theorem hull05_concreteRow
    (hc : ∀ b : Bad (nativePlaceSelection (lgpModelNativeData M)),
      rootHalfCoefficient (l := l) (lgpModelNativeData M) b =
        paperRootCoefficientFamily (lgpModelNativeData M) b)
    (G : ∀ b : Bad (nativePlaceSelection (lgpModelNativeData M)),
      PaperRootHullFormulaGap (lgpModelNativeData M) b)
    (hmatch : sourceVFormLogVolume =
      ∑ b : Bad (nativePlaceSelection (lgpModelNativeData M)),
        nativeBadLocalWeight (lgpModelNativeData M) b *
          Real.log (paperFormulaScalar (lgpModelNativeData M) b)) :
    ModelWeightedRootedIdentity M :=
  hull05_weightedIdentity_of_scaling (M := M) (by
    simpa [lgpNativeHaarFamily] using
      rootedScalingDecomposition_of_paperGap (T := lgpModelNativeData M) hc G) hmatch

/-- The three named inputs of the complete-proof row. -/
def hull05InputRows : List (String × String) :=
  [ ("hc coefficient identification", "named DATA (normalized generator supply; see S3132RootedCoefficientCorrectionActual)")
  , ("PaperRootHullFormulaGap per place", "named DATA (BadPlacePaperRootThetaHullActual:56/68)")
  , ("scalar-match equation", "named equation (the remaining arithmetic match)") ]

/-- The input record has three rows. -/
theorem hull05InputRows_length : hull05InputRows.length = 3 := rfl

#check hull05WeightedSum
#check hull05_weightedIdentity_of_scaling
#check hull05_concreteRow
#check hull05InputRows_length

end LeanFormal.IUT.XiFPaper.Hull05WeightedIdentityActual
end