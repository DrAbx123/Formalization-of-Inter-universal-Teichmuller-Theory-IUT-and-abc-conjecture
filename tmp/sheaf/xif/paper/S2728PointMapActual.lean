import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import tmp.sheaf.xif.paper.S2593TensorNormActual
import tmp.sheaf.xif.paper.S2595UnconditionalDictionaryActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
open scoped BigOperators
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2728PointMapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2593TensorNormActual
open LeanFormal.IUT.XiFPaper.S2595UnconditionalDictionaryActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b, MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b, BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b, Measure (qVFamTensorBlock T b))
variable [forall b, Measure.IsAddHaarMeasure (mu b)]
variable [forall b, SigmaFinite (mu b)]

/-- The actual mixed-prime global product carrier. -/
abbrev S2728Carrier : Type :=
  (b : Bad (nativePlaceSelection T)) -> qVFamTensorBlock T b

/-- The actual global point map `a c |-> (b |-> S2588PointMap T b a c)`. -/
noncomputable def S2728GlobalPointMap (a n c : Nat) :
    S2728Carrier T :=
  fun b => S2588PointMap T b a n c

@[simp] theorem S2728GlobalPointMap_apply (a n c : Nat)
    (b : Bad (nativePlaceSelection T)) :
    S2728GlobalPointMap T a n c b = S2588PointMap T b a n c := rfl

/-- Pointwise global q-pilot region: product of per-b q-pilot regions. -/
noncomputable def S2728GlobalQPilotRegion : Set (S2728Carrier T) :=
  Set.pi Set.univ (fun b => qPilotNormRegion T b)

/-- Pointwise global root hull: product of per-b root hulls. -/
noncomputable def S2728GlobalRootHull : Set (S2728Carrier T) :=
  Set.pi Set.univ (fun b => rootNormHull T b)

theorem S2728GlobalQPilotRegion_subset_rootHull :
    S2728GlobalQPilotRegion T ⊆
      S2728GlobalRootHull T := by
  intro x hx
  rw [Set.mem_pi] at hx ⊢
  intro b hb
  exact qPilotNormRegion_subset_rootNormHull T b (hx b hb)

/-- Region relation: the global point lies in the product q-pilot region exactly
when every fiber lies in the per-b q-pilot region. -/
theorem S2728GlobalPointMap_mem_QPilotRegion_iff (a n c : Nat) :
    S2728GlobalPointMap T a n c ∈
        S2728GlobalQPilotRegion (l := l) T ↔
      ∀ b, S2588PointMap T b a n c ∈ qPilotNormRegion (l := l) T b := by
  simp [S2728GlobalQPilotRegion, S2728GlobalPointMap]

theorem S2728GlobalPointMap_mem_RootHull_iff (a n c : Nat) :
    S2728GlobalPointMap T a n c ∈
        S2728GlobalRootHull (l := l) T ↔
      ∀ b, S2588PointMap T b a n c ∈ rootNormHull (l := l) T b := by
  simp [S2728GlobalRootHull, S2728GlobalPointMap]

/-- The actual product Haar measure on the global carrier. -/
noncomputable def S2728GlobalProductHaar : Measure (S2728Carrier T) :=
  Measure.pi (fun b => mu b)

/-- Volume relation: the global point singleton has product measure equal to
the product of the per-b point singleton measures. -/
theorem S2728GlobalPointMap_singleton_volume (a n c : Nat) :
    S2728GlobalProductHaar T mu
        {S2728GlobalPointMap T a n c} =
      ∏ b, mu b {S2588PointMap T b a n c} := by
  unfold S2728GlobalProductHaar S2728GlobalPointMap
  simpa using (Measure.pi_singleton (fun b => mu b)
    (fun b => S2588PointMap T b a n c))

/-- Per-fiber actual dictionary: for every ABC triple, the per-b point singleton
volume is bounded by the height. -/
theorem S2728GlobalPointMap_fiber_dictionary (a n c : Nat)
    (h : IsABCTriple a n c) (b : Bad (nativePlaceSelection T)) :
    ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
      {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
        (S2588PointMap T b a n c)}).toReal <=
      Height.logHeight₁ (abcRationalPoint a c) :=
  S2595Dictionary T b a n c h

#check S2728GlobalPointMap
#check S2728GlobalPointMap_apply
#check S2728GlobalPointMap_mem_QPilotRegion_iff
#check S2728GlobalPointMap_mem_RootHull_iff
#check S2728GlobalPointMap_singleton_volume
#check S2728GlobalPointMap_fiber_dictionary
#print axioms S2728GlobalPointMap_singleton_volume
#print axioms S2728GlobalPointMap_fiber_dictionary

end LeanFormal.IUT.XiFPaper.S2728PointMapActual
end
