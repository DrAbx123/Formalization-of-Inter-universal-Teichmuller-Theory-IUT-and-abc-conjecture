import tmp.sheaf.xif.paper.S1072CanonicalQ1URegionActual
import tmp.sheaf.xif.paper.S1073RootStackPaperThetaHullActual
import tmp.sheaf.xif.paper.S1085PushforwardHullEqActual
import tmp.sheaf.xif.paper.S1080PushforwardConstructionActual
import tmp.sheaf.xif.paper.S1079RootStackMeasureAuditActual
import tmp.sheaf.xif.paper.S1095PushforwardHullEqActual
import tmp.sheaf.xif.paper.S1102PushforwardHullPositivityActual
/-! # S1086: per-b q[1u] log <= root-stack theta hull log
Actual reduction: qPilot q[1u] region image contained in the root-stack paper
theta hull; pushforward measures identify both root-stack measures with qVFam
Haar; measure monotonicity gives the log inequality.  The geometric
containment, measurability and pushforward/Haar equalities are the exact inputs. -/
noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000
namespace LeanFormal.IUT.XiFPaper.S1086PerBQ1URootHullActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1085PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual
open LeanFormal.IUT.XiFPaper.S1079RootStackMeasureAuditActual
open LeanFormal.IUT.XiFPaper.S1095PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1102PushforwardHullPositivityActual
open MeasureTheory Topology
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- Exact geometric containment of the q[1u] image in the root-stack hull. -/
def S1086Q1UImageContainment : Prop :=
  rootStackEmbedding (l := l) T b '' qPilotQ1URegion (l := l) T b ⊆
    rootStackPaperThetaHull (l := l) T b
def S1086Q1URegionMeasurable : Prop :=
  MeasurableSet (rootStackEmbedding (l := l) T b ''
    qPilotQ1URegion (l := l) T b)
def S1086HaarEq : Prop :=
  s1080PushforwardHaar (l := l) T b = rootStackPaperThetaHaar (l := l) T b
/-- q[1u] log as the log of the qVFam Haar of its region. -/
noncomputable def qPilotQ1ULogHaar : Real :=
  Real.log ((Measure.addHaar : Measure (qVFamTensorBlock T b))
    (qPilotQ1URegion (l := l) T b)).toReal
/-- Actual pushforward image identity for the q[1u] region. -/
theorem s1086Q1UPushforward
    (hinj : S1085EmbeddingInjective (l := l) T b)
    (hmeas : S1085EmbeddingMeasurable (l := l) T b)
    (hS : S1086Q1URegionMeasurable (l := l) T b) :
    s1080PushforwardHaar (l := l) T b
      (rootStackEmbedding (l := l) T b '' qPilotQ1URegion (l := l) T b) =
      (Measure.addHaar : Measure (qVFamTensorBlock T b))
        (qPilotQ1URegion (l := l) T b) := by
  unfold s1080PushforwardHaar s1079HaarOnRange
  exact s1085Map_image_of_injective
    (Measure.addHaar : Measure (qVFamTensorBlock T b)) hmeas hinj hS
/-- Main per-b inequality from exact geometric/measure inputs. -/
theorem s1086PerB
    (hcont : S1086Q1UImageContainment (l := l) T b)
    (hinj : S1085EmbeddingInjective (l := l) T b)
    (hmeas : S1085EmbeddingMeasurable (l := l) T b)
    (hS : S1086Q1URegionMeasurable (l := l) T b)
    (hHaar : S1086HaarEq (l := l) T b)
    (hQ1UPos : 0 < (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b))
    (hQ1UFin : (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b) < ⊤)
    (hHullFin : rootStackPaperThetaHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) < ⊤) :
    qPilotQ1ULogHaar (l := l) T b ≤ rootStackPaperThetaHullLog (l := l) T b := by
  have hPushQ1U := s1086Q1UPushforward (l := l) T b hinj hmeas hS
  have hRegion : qPilotQ1URegion (l := l) T b ⊆
      paperLambdaORegion (l := l) T b (paperRootCoefficientFamily (l := l) T b) := by
    intro x hx
    have hx0 : rootStackEmbedding (l := l) T b x ∈
        rootStackEmbedding (l := l) T b '' qPilotQ1URegion (l := l) T b :=
      Set.mem_image_of_mem (rootStackEmbedding (l := l) T b) hx
    have hx' : rootStackEmbedding (l := l) T b x ∈
        rootStackPaperThetaHull (l := l) T b :=
      hcont hx0
    have hx'' := hx'
    rw [rootStackPaperThetaHull] at hx''
    rcases hx'' with ⟨y, hy, hyx⟩
    rw [hinj hyx] at hy
    exact hy
  have hmono : (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b) ≤
      rootStackPaperThetaHaar (l := l) T b
        (rootStackPaperThetaHull (l := l) T b) := by
    calc
      (Measure.addHaar : Measure (qVFamTensorBlock T b))
          (qPilotQ1URegion (l := l) T b)
          = s1080PushforwardHaar (l := l) T b
              (rootStackEmbedding (l := l) T b '' qPilotQ1URegion (l := l) T b) :=
            hPushQ1U.symm
      _ ≤ s1080PushforwardHaar (l := l) T b
            (rootStackEmbedding (l := l) T b ''
              paperLambdaORegion (l := l) T b
                (paperRootCoefficientFamily (l := l) T b)) :=
            measure_mono (Set.image_mono hRegion)
      _ = rootStackPaperThetaHaar (l := l) T b
            (rootStackPaperThetaHull (l := l) T b) := by
            rw [hHaar]
            rfl
  unfold qPilotQ1ULogHaar rootStackPaperThetaHullLog
  exact Real.log_le_log
    (ENNReal.toReal_pos hQ1UPos.ne' hQ1UFin.ne)
    (ENNReal.toReal_mono hHullFin.ne hmono)
/-- q[1u] log against the pushforward hull measure: no ambient Haar equality. -/
noncomputable def rootStackPaperThetaHullLogPushforward : Real :=
  Real.log ((s1080PushforwardHaar (l := l) T b
    (rootStackPaperThetaHull (l := l) T b)).toReal)

/-- Per-b inequality with s1080PushforwardHaar; the old S1086HaarEq is not
needed. -/
theorem s1086PerB_pushforward
    (hcont : S1086Q1UImageContainment (l := l) T b)
    (hinj : S1085EmbeddingInjective (l := l) T b)
    (hmeas : S1085EmbeddingMeasurable (l := l) T b)
    (hS : S1086Q1URegionMeasurable (l := l) T b)
    (hQ1UPos : 0 < (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b))
    (hQ1UFin : (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b) < ⊤)
    (hHullFin : s1080PushforwardHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) < ⊤) :
    qPilotQ1ULogHaar (l := l) T b ≤
      rootStackPaperThetaHullLogPushforward (l := l) T b := by
  have hPushQ1U := s1086Q1UPushforward (l := l) T b hinj hmeas hS
  have hRegion : qPilotQ1URegion (l := l) T b ⊆
      paperLambdaORegion (l := l) T b (paperRootCoefficientFamily (l := l) T b) := by
    intro x hx
    have hx0 : rootStackEmbedding (l := l) T b x ∈
        rootStackEmbedding (l := l) T b '' qPilotQ1URegion (l := l) T b :=
      Set.mem_image_of_mem (rootStackEmbedding (l := l) T b) hx
    have hx' : rootStackEmbedding (l := l) T b x ∈
        rootStackPaperThetaHull (l := l) T b :=
      hcont hx0
    rw [rootStackPaperThetaHull] at hx'
    rcases hx' with ⟨y, hy, hyx⟩
    rw [hinj hyx] at hy
    exact hy
  have hmono : (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b) ≤
      s1080PushforwardHaar (l := l) T b
        (rootStackPaperThetaHull (l := l) T b) := by
    calc
      (Measure.addHaar : Measure (qVFamTensorBlock T b))
          (qPilotQ1URegion (l := l) T b)
          = s1080PushforwardHaar (l := l) T b
              (rootStackEmbedding (l := l) T b '' qPilotQ1URegion (l := l) T b) :=
            hPushQ1U.symm
      _ ≤ s1080PushforwardHaar (l := l) T b
            (rootStackEmbedding (l := l) T b ''
              paperLambdaORegion (l := l) T b
                (paperRootCoefficientFamily (l := l) T b)) :=
            measure_mono (Set.image_mono hRegion)
      _ = s1080PushforwardHaar (l := l) T b
            (rootStackPaperThetaHull (l := l) T b) := rfl
  unfold qPilotQ1ULogHaar rootStackPaperThetaHullLogPushforward
  exact Real.log_le_log
    (ENNReal.toReal_pos hQ1UPos.ne' hQ1UFin.ne)
    (ENNReal.toReal_mono hHullFin.ne hmono)

/-- S1086 per-b with pushforward measure; S1102 supplies actual hull finiteness,
S1095 supplies actual injectivity. -/
theorem s1086PerB_pushforward_of_measurable
    (hcont : S1086Q1UImageContainment (l := l) T b)
    (h : S1102MeasurabilityInput (l := l) T b)
    (hS : S1086Q1URegionMeasurable (l := l) T b)
    (hQ1UPos : 0 < (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b))
    (hQ1UFin : (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b) < ⊤) :
    qPilotQ1ULogHaar (l := l) T b ≤
      rootStackPaperThetaHullLogPushforward (l := l) T b :=
  s1086PerB_pushforward (l := l) T b hcont
    (rootStackEmbedding_injective_actual (l := l) T b) h.1 hS hQ1UPos hQ1UFin
    (s1102Hull_finiteness_actual (l := l) T b h)


end LeanFormal.IUT.XiFPaper.S1086PerBQ1URootHullActual