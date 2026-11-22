import tmp.sheaf.n8.closure.O4ConstructedHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealEdgeNormalizationReduction
import Mathlib

/-!
# O4 bounded hull construction

Restrict the source scaling units to nonpositive log-degree (the paper's
contractive scalings), define the bounded holomorphic hull with this restricted
scaling set, and prove that its volume equals the image-union volume whenever
every theta-pilot image has nonpositive log-degree.  No arbitrary scaling or
hull is introduced; the restricted scaling set is an actual subset of
sourceScalingUnits.
-/

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory

namespace LeanFormal.IUT.N8Closure.O4BoundedHullConstruction

universe ua uv upi umon ui u v w

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- Actual contractive source scalings: sourceScalingUnits with degree <= 0. -/
def boundedScalingUnits : Set (I.ThetaPilotPoint v) :=
  {s | s ∈ I.sourceScalingUnits v ∧ I.sourceLocalLogDegree v s ≤ 0}

/-- Bounded holomorphic hull, using only contractive scalings. -/
noncomputable def boundedHull : Submonoid (I.ThetaPilotPoint v) :=
  holomorphicHull (boundedScalingUnits I v) (I.possibleThetaPilotImageSet v R n)

/-- Bounded hull volume. -/
noncomputable def boundedHullVolume : ENNReal :=
  I.sourceSetVolume v (boundedHull I v R n : Set (I.ThetaPilotPoint v))

/-- Actual image-union volume. -/
noncomputable def imageVolume : ENNReal := I.sourceImageVolume v R n

/-- The nonpositive-degree points form a submonoid. -/
noncomputable def nonpositiveSubmonoid : Submonoid (I.ThetaPilotPoint v) where
  carrier := {x | I.sourceLocalLogDegree v x ≤ 0}
  one_mem' := by
    change I.sourceLocalLogDegree v (1 : I.ThetaPilotPoint v) ≤ 0
    rw [I.sourceLocalLogDegree_one]
  mul_mem' := by
    intro x y hx hy
    change I.sourceLocalLogDegree v (x * y) ≤ 0
    rw [I.sourceLocalLogDegree_mul]
    exact add_nonpos hx hy

/-- The nonpositive-degree submonoid is a candidate hull for the bounded
scalings. -/
theorem nonpositiveSubmonoid_candidate :
    CandidateHull (boundedScalingUnits I v) (nonpositiveSubmonoid I v) := by
  intro s hs x hx
  change I.sourceLocalLogDegree v (s * x) ≤ 0
  rw [I.sourceLocalLogDegree_mul]
  exact add_nonpos hs.2 hx

/-- If every theta-pilot image has nonpositive degree, the whole bounded hull
has nonpositive degree. -/
theorem boundedHull_nonpositive
    (himg : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0) :
    (boundedHull I v R n : Set (I.ThetaPilotPoint v)) ⊆
      (nonpositiveSubmonoid I v : Set (I.ThetaPilotPoint v)) := by
  apply holomorphicHull_le
    (nonpositiveSubmonoid_candidate I v)
  intro x hx
  obtain ⟨j, rfl⟩ := (I.mem_possibleThetaPilotImageSet_iff v R n x).mp hx
  exact himg j

/-- Bounded hull volume is zero under image-side nonpositivity. -/
theorem boundedHullVolume_eq_zero
    (himg : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0) :
    boundedHullVolume I v R n = 0 := by
  unfold boundedHullVolume
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    exact le_of_eq (I.sourcePointVolume_eq_zero_of_logDegree_nonpos v x
      (boundedHull_nonpositive I v R n himg hx))
  · exact zero_le

/-- Image volume is zero under image-side nonpositivity. -/
theorem imageVolume_eq_zero
    (himg : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0) :
    imageVolume I v R n = 0 := by
  unfold imageVolume sourceImageVolume sourceSetVolume
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    obtain ⟨j, rfl⟩ := (I.mem_possibleThetaPilotImageSet_iff v R n x).mp hx
    rw [I.sourcePointVolume_eq_zero_of_logDegree_nonpos v
      (I.sourceThetaPilotPoint v R n j) (himg j)]
  · exact zero_le

/-- Bounded-hull via-images identity: under image-side nonpositivity, the
bounded hull volume equals the image volume. -/
theorem boundedHull_volume_eq_imageVolume
    (himg : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0) :
    boundedHullVolume I v R n = imageVolume I v R n := by
  rw [boundedHullVolume_eq_zero I v R n himg,
    imageVolume_eq_zero I v R n himg]

end LeanFormal.IUT.N8Closure.O4BoundedHullConstruction
