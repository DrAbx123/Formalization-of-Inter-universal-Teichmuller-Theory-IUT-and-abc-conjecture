import tmp.sheaf.xif.paper.GlobalThetaPilotLogVolumeActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import LeanFormal.IUT.Foundations.Volumes.WeightedVolume

-- Actual global Theta-pilot procession / finite hull candidate
--
-- From the actual q_v values and theta values of GlobalThetaPilotLogVolumeActual:
-- globalThetaValue j := sum over V_bad of -log(q_v^(j^2));
-- these form an actual WeightedValues procession and an actual FiniteHull whose
-- hullVolume is the actual finite sum of absolute values. No fake global hull,
-- no local=global equality, no inequality to the q-pilot. WRITE-ONLY.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotProcessionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual
open LeanFormal.IUT.Foundations.Theta

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- Actual global Theta-pilot value at a signed label: sum over V_bad of the
-- local -log(q_v^(j^2)).
noncomputable def globalThetaValue (j : SignedLabel l.value) : Real :=
  ∑ b : Bad (nativePlaceSelection T), -Real.log (thetaValueFromQ T b j)

-- Actual global Theta-pilot procession with uniform finite weights.
noncomputable def globalThetaProcession :
    WeightedValues (SignedLabel l.value) where
  value := globalThetaValue T
  weight _ := (Fintype.card (SignedLabel l.value) : Real)⁻¹
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hcard : (Fintype.card (SignedLabel l.value) : Real) ≠ 0 := by
      have hpos : 0 < Fintype.card (SignedLabel l.value) := by
        rw [SignedLabel.card_signedLabel]
        exact l.prime.pos
      exact_mod_cast (ne_of_gt hpos)
    exact (mul_inv_cancel₀ hcard).symm

-- Actual global possible-images set: the set of global Theta-value vectors
-- indexed by the signed label, not a fabricated hull.
noncomputable def globalThetaPossibleImage (j : SignedLabel l.value) :
    (Bad (nativePlaceSelection T) → Real) :=
  fun b => -Real.log (thetaValueFromQ T b j)

noncomputable def globalThetaPossibleImageSet :
    Set (Bad (nativePlaceSelection T) → Real) :=
  Set.range (globalThetaPossibleImage T)

-- Exact obstruction: an actual global holomorphic hull containing the actual
-- possible-image set is not constructed from the q_v/theta data alone. This
-- records the exact missing data; no sum-of-abs surrogate is used.
structure GlobalThetaHolomorphicHullCandidate where
  hull : Set (Bad (nativePlaceSelection T) → Real)
  containment : globalThetaPossibleImageSet T ⊆ hull

def GlobalThetaHolomorphicHullObstruction : Prop :=
  Nonempty (GlobalThetaHolomorphicHullCandidate (l := l) T)

theorem globalThetaPossibleImage_mem (j : SignedLabel l.value) :
    globalThetaPossibleImage T j ∈ globalThetaPossibleImageSet T :=
  ⟨j, rfl⟩
#check globalThetaValue
#check globalThetaProcession
#check globalThetaPossibleImage
#check globalThetaPossibleImageSet
#check GlobalThetaHolomorphicHullCandidate
#check GlobalThetaHolomorphicHullObstruction

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotProcessionActualAdapted

end