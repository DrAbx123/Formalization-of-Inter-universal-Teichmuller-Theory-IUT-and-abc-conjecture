import tmp.sheaf.xif.paper.PaperLambdaOHullActual
import tmp.sheaf.xif.paper.PaperMuLogIQCarrierActual
import tmp.sheaf.xif.paper.UnitSmulCanonicalUnitReferenceActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-!
# Actual Haar mu_log on the unit lambda-O hull

paperLambdaOHull is an intersection of actual unit-scaled regions.  A candidate
paperLambdaOScaledRegion u is exactly (u : Block) * O, so its actual Haar
measure is positive and finite by the unit-smul canonical-reference theorem.
If the intersection hull equals a candidate, the hull measure and normalized
mu_log follow by equality; otherwise the exact candidate-equality gap is kept.
No closure and no assumed positivity is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperLambdaOHullHaarActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperLambdaOHullActual
open LeanFormal.IUT.XiFPaper.PaperMuLogIQCarrierActual
open LeanFormal.IUT.XiFPaper.UnitSmulCanonicalUnitReferenceActual
open MeasureTheory

universe u

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {l : PrimeGeFive}
variable {V : Type} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
variable [MeasurableSpace (Block (G := G))]
variable [BorelSpace (Block (G := G))]
variable (mu : Measure (Block (G := G)))
variable [Measure.IsAddHaarMeasure mu]

/-- The actual tensor places of the Block. -/
abbrev lambdaOPlaces : (v : V) → Unit → FinitePlaceAtPrime K p :=
  fun v _ => G.place v

/-- The actual tensor tuple. -/
abbrev lambdaOTuple : (v : V) → Unit := fun _ => ()

/-- Actual unit-scaled candidate as a set smul of O. -/
theorem paperLambdaOScaledRegion_eq_smul (u : (Block (G := G))ˣ) :
    paperLambdaOScaledRegion (G := G) u =
      (u : Block (G := G)) • paperUnitReference (G := G) := by
  ext x
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, by simp [smul_eq_mul]⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, by simp [smul_eq_mul]⟩

/-- Candidate Haar positivity/finiteness, actual from unit smul. -/
theorem paperLambdaOScaledRegion_measure_pos_lt_top
    (u : (Block (G := G))ˣ) :
    0 < mu (paperLambdaOScaledRegion (G := G) u) ∧
      mu (paperLambdaOScaledRegion (G := G) u) < ⊤ := by
  rw [paperLambdaOScaledRegion_eq_smul]
  exact measure_unit_smul_canonicalUnitReference_pos_lt_top
    (p := p) (lambdaOPlaces (G := G)) (lambdaOTuple (V := V)) mu u

/-- Actual normalized mu_log of a candidate. -/
noncomputable def paperLambdaOCandidateLog (u : (Block (G := G))ˣ) : Real :=
  arithmeticTupleNormalizedLogVolume (lambdaOPlaces (G := G))
    (lambdaOTuple (V := V)) mu (paperLambdaOScaledRegion (G := G) u)

/-- Exact candidate equality gap for the infinite intersection hull. -/
structure PaperLambdaOHullCandidateGap where
  candidate : (Block (G := G))ˣ
  hull_eq_candidate :
    paperLambdaOHull (G := G) (l := l) =
      paperLambdaOScaledRegion (G := G) candidate

/-- The candidate equality gap is exactly a unit whose scaled region is the hull. -/
def PaperLambdaOHullCandidateGapRequired : Prop :=
  Nonempty (PaperLambdaOHullCandidateGap (G := G) (l := l))

/-- Conditional actual normalized mu_log on the hull from candidate equality. -/
noncomputable def paperLambdaOHullLogOfCandidate
    (H : PaperLambdaOHullCandidateGap (G := G) (l := l)) : Real :=
  paperLambdaOCandidateLog (G := G) mu H.candidate

/-- Under candidate equality, the hull has actual positive finite Haar measure. -/
theorem paperLambdaOHull_measure_pos_lt_top_of_candidate
    (H : PaperLambdaOHullCandidateGap (G := G) (l := l)) :
    0 < mu (paperLambdaOHull (G := G) (l := l)) ∧
      mu (paperLambdaOHull (G := G) (l := l)) < ⊤ := by
  rw [H.hull_eq_candidate]
  exact paperLambdaOScaledRegion_measure_pos_lt_top (G := G) mu H.candidate

/-- The candidate log computed on the hull is the candidate normalized log. -/
theorem paperLambdaOHullLogOfCandidate_eq
    (H : PaperLambdaOHullCandidateGap (G := G) (l := l)) :
    paperLambdaOHullLogOfCandidate (G := G) mu H =
      arithmeticTupleNormalizedLogVolume (lambdaOPlaces (G := G))
        (lambdaOTuple (V := V)) mu (paperLambdaOHull (G := G) (l := l)) := by
  unfold paperLambdaOHullLogOfCandidate paperLambdaOCandidateLog
  rw [H.hull_eq_candidate]

/-- Actual paper mu_log on the same carrier with unit region O. -/
noncomputable def paperLambdaOIQCarrier :
    IQHullLogVolumeInterface (Block (G := G)) :=
  paperMuLogIQCarrier (lambdaOPlaces (G := G)) (lambdaOTuple (V := V)) mu

/-- The carrier's logVolume is the actual Haar log-volume. -/
theorem paperLambdaOIQCarrier_logVolume :
    (paperLambdaOIQCarrier (G := G) mu).logVolume =
      paperMuLogHaar (lambdaOPlaces (G := G)) (lambdaOTuple (V := V)) mu :=
  paperMuLogIQCarrier_logVolume (lambdaOPlaces (G := G)) (lambdaOTuple (V := V)) mu

end LeanFormal.IUT.XiFPaper.PaperLambdaOHullHaarActual

end