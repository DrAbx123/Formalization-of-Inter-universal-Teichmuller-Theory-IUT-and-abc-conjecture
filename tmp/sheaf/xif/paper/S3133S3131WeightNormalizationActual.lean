import tmp.sheaf.xif.paper.S3133QPilotLogVolumeSignActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.W6ActualPilotMonodromyActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

/-!
# Remark 3.1.1 weight normalization: raw total and total-one normalized family

Source: IUT III, Remark 3.1.1, (ii)-(iv), p. 95-97 (iut3.txt lines 5590-5747):
the normalized log-volume of a direct product region is the weighted sum with
weights 1/N_v, N_v a product of completion degrees [K_w:(F_mod)_v], and a
"suitable positive real normalization factor" may be applied.

COMPONENT, not a paper object.  Named future consumer: mainline Stage-2
model map field M4 of S3131Stage2ModelMapActual (same-C model map, IUT III
Definition 3.8(i) / Remark 3.1.1).  Statements supplied here:

* S3131WeightSum: the actual total of the normalized weights
  nativeBadLocalWeight T b = 1/[K_w:(F_mod)_v];
* each weight is positive (actual completion degree at least one);
* S3131WeightSumOneHypothesis: the exact proposition that the RAW actual total
  equals one.  It is NOT a theorem of the actual definitions (e.g. if all
  completion degrees are one the raw total is card V_bad); this is the exact
  residual hypothesis for the unnormalized M4 reading;
* S3131NormalizedWeight := weight / weightSum with PROVED total one
  (S3131NormalizedWeightTotal): the paper's suitable positive normalization
  factor applied to the actual Remark 3.1.1 weights.  This is the concrete
  unconditionally available total-one family (V_bad nonempty).

No weight equality is assumed.  No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3133S3131WeightNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.W6ActualPilotMonodromyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]

/-- The actual total of the Remark 3.1.1 normalized weights over V_bad. -/
noncomputable def S3131WeightSum : Real :=
  ∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b

/-- Each actual Remark 3.1.1 normalized weight is positive. -/
theorem S3131WeightTerm_pos (b : Bad (nativePlaceSelection T)) :
    0 < nativeBadLocalWeight T b :=
  nativeBadLocalWeight_pos T b

/-- The actual total normalized weight is positive when V_bad is nonempty. -/
theorem S3131WeightSum_pos [Nonempty (Bad (nativePlaceSelection T))] :
    0 < S3131WeightSum T := by
  unfold S3131WeightSum
  apply Finset.sum_pos
  · intro b _
    exact S3131WeightTerm_pos T b
  · exact Finset.univ_nonempty

/-- The concrete total-one weight family: the actual weights divided by their
actual total (Remark 3.1.1 suitable positive normalization factor). -/
noncomputable def S3131NormalizedWeight (b : Bad (nativePlaceSelection T)) : Real :=
  nativeBadLocalWeight T b / S3131WeightSum T

/-- The normalized weights sum to one (concrete total-one form of mainline M4). -/
theorem S3131NormalizedWeightTotal [Nonempty (Bad (nativePlaceSelection T))] :
    (∑ b : Bad (nativePlaceSelection T), S3131NormalizedWeight T b) = 1 := by
  unfold S3131NormalizedWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (S3131WeightSum_pos T))

/-- The exact proposition that the RAW actual weight total is one: the residual
hypothesis for the unnormalized M4 reading, not a theorem. -/
def S3131WeightSumOneHypothesis : Prop :=
  S3131WeightSum T = 1

end LeanFormal.IUT.XiFPaper.S3133S3131WeightNormalizationActual
