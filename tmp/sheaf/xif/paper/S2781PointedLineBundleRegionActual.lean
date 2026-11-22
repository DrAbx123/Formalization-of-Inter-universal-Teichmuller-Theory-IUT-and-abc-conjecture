import tmp.sheaf.xif.paper.S2735QPilotLineBundleActual
import tmp.sheaf.xif.paper.S2752ExtendedSupportIdealActual
import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.RingTheory.FractionalIdeal.Norm

noncomputable section
open scoped ENNReal nonZeroDivisors Classical
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2752ExtendedSupportIdealActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol

variable (l : PrimeGeFive)

/-- Carrier: nonzero fractional line bundles. -/
abbrev S2781Carrier : Type :=
  (SourceLineBundle (A := S2735Arithmetic l))ˣ

/-- Actual lattice covolume log of a pointed line bundle. -/
noncomputable def S2781CovolumeLog (y : S2781Carrier l) : Real :=
  Real.log ((FractionalIdeal.absNorm (y.1) : ℚ) : Real)

/-- Set-level log-volume: supremum of the pointed covolume logs. -/
noncomputable def S2781PointedLogVolume
    (S : Set (S2781Carrier l)) : ENNReal :=
  ⨆ y : S, ENNReal.ofReal (S2781CovolumeLog l y.1)


theorem S2781PointedLogVolume_le_of_mem
    {S : Set (S2781Carrier l)} {x : S2781Carrier l} (hx : x ∈ S) :
    ENNReal.ofReal (S2781CovolumeLog l x) ≤ S2781PointedLogVolume l S := by
  unfold S2781PointedLogVolume
  exact le_iSup (fun y : S => ENNReal.ofReal (S2781CovolumeLog l y.1))
    ⟨x, hx⟩

theorem S2781PointedLogVolume_mono {S T : Set (S2781Carrier l)}
    (hST : S ⊆ T) :
    S2781PointedLogVolume l S ≤ S2781PointedLogVolume l T := by
  refine iSup_le fun y : S => ?_
  exact le_iSup (fun z : T =>
    ENNReal.ofReal (S2781CovolumeLog l z.1)) ⟨y.1, hST y.2⟩

theorem S2781PointedLogVolume_singleton_lt_top (x : S2781Carrier l) :
    S2781PointedLogVolume l ({x} : Set (S2781Carrier l)) < ⊤ := by
  have h : S2781PointedLogVolume l ({x} : Set (S2781Carrier l)) ≤
      ENNReal.ofReal (S2781CovolumeLog l x) := by
    refine iSup_le fun y => ?_
    have hy : y.1 = x := Set.mem_singleton_iff.mp y.2
    rw [hy]
  exact lt_of_le_of_lt h ENNReal.ofReal_lt_top

/-- Pointed IQ-hull: image/hull/unitRegion are the single point `x`, the
scaling is the identity, and the log-volume is the actual lattice-covolume
supremum. -/
noncomputable def S2781PointedIQHull (x : S2781Carrier l) :
    IQHullLogVolumeInterface (S2781Carrier l) where
  imageSet := {x}
  hull := {x}
  imageSet_subset_hull := subset_rfl
  logVolume := S2781PointedLogVolume l
  logVolume_mono := by
    intro S T hST
    exact S2781PointedLogVolume_mono l hST
  unitRegion := {x}
  scaleShift := id
  hull_subset_scaleShift := by
    intro y hy
    exact ⟨y, hy, rfl⟩
  unitRegion_logVolume_lt_top := S2781PointedLogVolume_singleton_lt_top l x
  scaleShift_unitRegion_logVolume_le := by
    rw [Set.image_id]

#check S2781Carrier
#check S2781CovolumeLog
#check S2781PointedLogVolume
#check S2781PointedLogVolume_mono
#check S2781PointedLogVolume_singleton_lt_top
#check S2781PointedIQHull
#print axioms S2781PointedIQHull


/-- The actual q-pilot pointed line bundle (falls back to the unit point only if
the fractional line bundle is zero). -/
noncomputable def S2781QPilotPoint (a b c : Nat) : S2781Carrier l :=
  if h : qPilotLineBundleExtended l
      (S2752FinalHweightvolActual.S2752J l a b c) = 0
  then 1
  else Units.mk0 _ h

/-- Candidate bridge logShellPoint, now genuinely point-dependent. -/
noncomputable def S2781LogShellPoint (a b c : Nat) : S2781Carrier l :=
  S2781QPilotPoint l a b c

/-- Pointed comparison region on the pointed IQ-hull. -/
noncomputable def S2781ComparisonRegion (eps : Real) (a n c : Nat) :
    Set (S2781Carrier l) :=
  normalizedComparisonRegion (S2781PointedIQHull l 1)
    (S2781LogShellPoint l) a n c

/-- Explicit height and region/weight gaps for the pointed comparison. -/
structure S2781Gap (eps : Real) where
  height_le_region :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) *
          ((S2781PointedIQHull l 1).logVolume
            (S2781ComparisonRegion l eps a b c)).toReal
  region_le_weight :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      ((S2781PointedIQHull l 1).logVolume
        (S2781ComparisonRegion l eps a b c)).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((S2781PointedIQHull l 1).logVolume
            (S2781PointedIQHull l 1).hull).toReal + D

/-- Conditional epsilon comparison on the pointed carrier: both paper gaps are
explicit hypotheses. -/
noncomputable def S2781EpsilonComparisonOfGap (eps : Real)
    (G : S2781Gap l eps) :
    Cor312EpsilonArithmeticComparison (S2781PointedIQHull l 1) eps where
  logShellPoint := S2781LogShellPoint l
  height_le_normalizedRegionVolume := G.height_le_region
  regionVolume_le_normalizedWeight := G.region_le_weight


/-- The pointed comparison region is exactly the unit point together with the
q-pilot point: its log-volume genuinely depends on the point. -/
theorem S2781ComparisonRegion_eq (eps : Real) (a n c : Nat) :
    S2781ComparisonRegion l eps a n c =
      ({1} : Set (S2781Carrier l)) ∪ {S2781LogShellPoint l a n c} := by
  simp [S2781ComparisonRegion, normalizedComparisonRegion, S2781PointedIQHull]

#check S2781QPilotPoint
#check S2781LogShellPoint
#check S2781ComparisonRegion
#check S2781ComparisonRegion_eq
#check S2781Gap
#check S2781EpsilonComparisonOfGap
#print axioms S2781EpsilonComparisonOfGap


/-- S2752 hweightvol connects to the pointed region: when the q-pilot point is
nonzero, the comparison region's log-volume dominates the arithmetic weight. -/
theorem S2781_weight_le_regionVolume_of_ne
    (a b c : Nat) (habc : IsABCTriple a b c)
    (hne : qPilotLineBundleExtended l
      (S2752FinalHweightvolActual.S2752J l a b c) ≠ 0) :
    ENNReal.ofReal (arithmeticWeight (abcRationalPoint a c)) ≤
      (S2781PointedIQHull l 1).logVolume
        (S2781ComparisonRegion l 0 a b c) := by
  have hw : arithmeticWeight (abcRationalPoint a c) ≤
      S2736QPilotLineBundleLogVolume (l := l)
        (S2752FinalHweightvolActual.S2752J l a b c) := by
    simpa using S2752_hweightvol l a b c habc
  have hpoint : S2781LogShellPoint l a b c =
      Units.mk0 (qPilotLineBundleExtended l
        (S2752FinalHweightvolActual.S2752J l a b c)) hne := by
    unfold S2781LogShellPoint S2781QPilotPoint
    rw [dif_neg hne]
  have hcov : S2781CovolumeLog l (S2781LogShellPoint l a b c) =
      S2736QPilotLineBundleLogVolume (l := l)
        (S2752FinalHweightvolActual.S2752J l a b c) := by
    rw [hpoint]
    rfl
  have hmem : S2781LogShellPoint l a b c ∈
      ({1} : Set (S2781Carrier l)) ∪ {S2781LogShellPoint l a b c} := by simp
  rw [S2781ComparisonRegion_eq]
  have hle : ENNReal.ofReal
        (S2781CovolumeLog l (S2781LogShellPoint l a b c)) ≤
      (S2781PointedIQHull l 1).logVolume
        (({1} : Set (S2781Carrier l)) ∪ {S2781LogShellPoint l a b c}) := by
    exact S2781PointedLogVolume_le_of_mem l hmem
  exact le_trans (ENNReal.ofReal_le_ofReal (by rw [hcov]; exact hw)) hle

#check S2781_weight_le_regionVolume_of_ne
#print axioms S2781_weight_le_regionVolume_of_ne

end LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual
end
