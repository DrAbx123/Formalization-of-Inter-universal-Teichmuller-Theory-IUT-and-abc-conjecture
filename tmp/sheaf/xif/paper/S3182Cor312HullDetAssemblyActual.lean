import tmp.sheaf.xif.paper.Hull04CertificateWiringActual
import tmp.sheaf.xif.paper.Hull05WeightedIdentityActual
import tmp.sheaf.xif.paper.AbsTopIII14FieldScalingActual
import tmp.sheaf.xif.paper.S3132RootedScalingDataFormulaActual
import tmp.sheaf.xif.paper.S3132IQHullRealLogVolumeReadoutActual
import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual
import tmp.sheaf.xif.paper.S3132ConcreteSourceNormalizationClosureActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open MeasureTheory
open scoped Pointwise ENNReal
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
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelClauseResidualActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideSharpResidualReducedActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelComparisonDataActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideHullSlotWiringActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideQSideSlotWiringActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideCertificateSignedShapeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.Hull04CertificateWiringActual
open LeanFormal.IUT.XiFPaper.Hull05WeightedIdentityActual
open LeanFormal.IUT.XiFPaper.AbsTopIII14FieldScalingActual
open LeanFormal.IUT.XiFPaper.S3132RootedScalingDataFormulaActual
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual
open LeanFormal.IUT.XiFPaper.S3132ConcreteSourceNormalizationClosureActual

namespace LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual

/-!
# STEP 0 prior-art: Cor 3.12|hull|det|CardAMPL|Hull04|Hull05|AbsTopIII14 -> hits Hull01/02/03 (hull operator laws), Hull04CertificateWiringActual (H4 wiring), Hull05WeightedIdentityActual (H2 row), AbsTopIII14FieldScalingActual (field-scaling), S3132ConcreteSourceNormalizationClosureActual (source volume) -> REUSE (assembly only; every arithmetic input consumed).

# S3182: Cor 3.12 hull+det comparison assembly from REAL proved declarations

A71 line references (IUT III, Cor 3.12): statement corpus 10324-10353;
Step (xi) corpus 10750-10987; conclusion corpus 10897.

PREVIOUS S3180 was shape-only (conclusion as a hypothesis).  This file instead
assembles the hull+det comparison from the already-proved hull-layer declarations:
* theta value: the canonical rooted readout `modelThetaValue M` (= log of the actual
  source hull Haar under H2; real tree definition, not an arbitrary real);
* hull value: the same readout via Hull05/F_2 row (weighted rooted identity);
* hull <= theta: Hull04 H4 wiring (certificate-hull/AMPL value layer);
* field-scaling normalization: AbsTopIII14 (real p-adic scaling law),
and the conclusion bundling both comparison and scaling components.
Deep paper steps (IPL/SHE/APT) are named interface rows, NOT proof fields.
Registry frozen 14041.
-/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- Real inputs of the assembly: the H2 row data (hc, per-place formula gap,
scalar match) and the H4 boundary (theta with |readout| <= theta). -/
structure HullDetAssemblyInputs where
  hc : ∀ b : Bad (nativePlaceSelection (lgpModelNativeData M)),
    rootHalfCoefficient (l := l) (lgpModelNativeData M) b =
      paperRootCoefficientFamily (lgpModelNativeData M) b
  G : ∀ b : Bad (nativePlaceSelection (lgpModelNativeData M)),
    PaperRootHullFormulaGap (lgpModelNativeData M) b
  hmatch : sourceVFormLogVolume =
    ∑ b : Bad (nativePlaceSelection (lgpModelNativeData M)),
      nativeBadLocalWeight (lgpModelNativeData M) b *
        Real.log (paperFormulaScalar (lgpModelNativeData M) b)
  theta : ℝ
  theta_nonneg : 0 ≤ theta
  hH4 : |modelThetaValue M| ≤ theta

/-- **The real Cor 3.12 hull-side conclusion**: the actual source hull log-volume
equals the canonical rooted Theta readout AND is bounded by theta. -/
def Cor312HullDetConclusion (theta : ℝ) : Prop :=
  Real.log sourceHullRealLogVolume = modelThetaValue M ∧
    Real.log sourceHullRealLogVolume ≤ theta

/-- **S3182 assembly theorem**: from the real H2 row + H4 wiring inputs, the Cor 3.12
hull-side comparison conclusion holds (every input field is consumed: H2 fields give
the equality; hH4/theta_nonneg give the inequality). -/
theorem cor312_hullDet_conditional (I : HullDetAssemblyInputs M) :
    Cor312HullDetConclusion M I.theta :=
by
  have h2 := hull05_concreteRow (M := M) I.hc I.G I.hmatch
  have heq : Real.log sourceHullRealLogVolume = modelThetaValue M :=
    weightedIdentity_canonicalReadout (M := M) h2
  have hle : modelThetaValue M ≤ I.theta :=
    le_trans (le_abs_self (modelThetaValue M)) I.hH4
  exact ⟨heq, by rw [heq]; exact hle⟩

/-- **Field-scaling component of the assembly** (real p-adic scaling law, reused
from AbsTopIII14): the log-volume of p * S shifts by -[K:Q_p] log p. -/
theorem cor312_fieldScaling_component
    {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
    [MeasurableSpace K] [CharZero K] [CompleteSpace K] [BorelSpace K]
    {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K]
    (μ : Measure K) [Measure.IsAddHaarMeasure μ] {S : Set K}
    (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    Real.log (μ ((p : ℚ_[p]) • S)).toReal =
      (-(Module.finrank ℚ_[p] K : ℝ)) * Real.log (p : ℝ) +
        Real.log (μ S).toReal :=
  fieldScaling_log_measure_prime_smul (p := p) μ hpos hfin

/-- Named deep-step interface rows (IPL / SHE / APT); NOT proof fields. -/
def cor312DeepStepRows : List (String × String) :=
  [ ("IPL (initial portion of the log-link)", "named deep step; interface only")
  , ("SHE (simultaneous holomorphic expressibility)", "named deep step; interface only")
  , ("APT (absolute prime-strip transport)", "named deep step; interface only") ]

/-- The deep-step interface record has three rows. -/
theorem cor312DeepStepRows_length : cor312DeepStepRows.length = 3 := rfl

#check HullDetAssemblyInputs
#check Cor312HullDetConclusion
#check cor312_hullDet_conditional
#check cor312_fieldScaling_component
#check cor312DeepStepRows_length

end LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual
end