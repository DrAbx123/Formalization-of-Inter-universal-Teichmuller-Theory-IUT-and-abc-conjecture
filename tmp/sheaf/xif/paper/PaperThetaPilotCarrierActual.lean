import tmp.sheaf.xif.paper.ThetaPilotHullProcessionActual
import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import LeanFormal.IUT.Foundations.Arithmetic.FiniteLabels
import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

/-! # Actual paper Theta-pilot carrier on F_l^x

The project's ThetaPilotCarrier is Fin (lStar+1), which is not the paper's label
set F_l^x.  This file constructs the actual paper carrier

  PaperThetaPilotCarrier = (ZMod l.value)^x = F_l^x

together with the actual procession labels, theta values from the V_bad base q
collection, the possible-image points, and the actual holomorphic hull on this
F_l^x-indexed carrier.

The theta values are q_v^(j^2) with the centered integer representative j of a
unit of ZMod l; possible images are the value points obtained by placing one
theta value at every F_l^x label; the hull is the generic value-realized
holomorphic hull (SourceImageHull.holomorphicHull) with the actual scaling
units.

No old Fin(lStar+1) carrier, no raw-substitution of -|log Theta|, and no fake
equivalence is used.  No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.Foundations.Theta
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull
open scoped BigOperators

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual paper Theta-pilot carrier: F_l^x, not Fin(lStar+1). -/
abbrev PaperThetaPilotCarrier : Type := (ZMod l.value)ˣ

/-- The centered integer representative of a unit label. -/
def paperLabelInt (j : PaperThetaPilotCarrier (l := l)) : Int :=
  if j.val.val <= lStar l.value then (j.val.val : Int)
  else (j.val.val : Int) - (l.value : Int)

/-- The Gaussian exponent of a paper label. -/
def paperGaussExponent (j : PaperThetaPilotCarrier (l := l)) : Nat :=
  (gaussExponent (paperLabelInt (l := l) j)).toNat

/-- The actual theta value q^(j^2) at a real q and paper label j. -/
noncomputable def paperThetaValue (q : Real) (j : PaperThetaPilotCarrier (l := l)) : Real :=
  q ^ paperGaussExponent (l := l) j

theorem paperThetaValue_pos {q : Real} (hq : 0 < q)
    (j : PaperThetaPilotCarrier (l := l)) :
    0 < paperThetaValue (l := l) q j :=
  pow_pos hq _

theorem paperThetaValue_log {q : Real} {j : PaperThetaPilotCarrier (l := l)} :
    Real.log (paperThetaValue (l := l) q j) =
      (paperGaussExponent (l := l) j : Real) * Real.log q := by
  unfold paperThetaValue
  rw [Real.log_pow]

/-- The actual paper Theta-pilot value carrier: one real value for every
F_l^x label. -/
abbrev PaperThetaPilotPoint : Type :=
  PaperThetaPilotCarrier (l := l) -> Multiplicative Real

/-- The actual theta-pilot point determined by a real q and a label j. -/
noncomputable def paperThetaPilotPointAt (q : Real)
    (j : PaperThetaPilotCarrier (l := l)) : PaperThetaPilotPoint (l := l) :=
  fun _ => Multiplicative.ofAdd (Real.log (paperThetaValue (l := l) q j))

/-- The actual possible-image union at real q: the F_l^x-indexed theta-value
points. -/
noncomputable def paperPossibleImageSet (q : Real) :
    Set (PaperThetaPilotPoint (l := l)) :=
  Set.range (paperThetaPilotPointAt (l := l) q)

/-- Actual scaling units of the value carrier (every label nontrivial). -/
def paperScalingUnits : Set (PaperThetaPilotPoint (l := l)) :=
  {s | ∀ j : PaperThetaPilotCarrier (l := l), s j ≠ 1}

/-- The actual holomorphic hull of the paper possible images on F_l^x. -/
noncomputable def paperThetaPilotHull (q : Real) :
    Submonoid (PaperThetaPilotPoint (l := l)) :=
  holomorphicHull (paperScalingUnits (l := l))
    (paperPossibleImageSet (l := l) q)

theorem paperPossibleImage_subset_hull (q : Real) :
    paperPossibleImageSet (l := l) q ⊆
      (paperThetaPilotHull (l := l) q : Set (PaperThetaPilotPoint (l := l))) :=
  subset_holomorphicHull

theorem paperThetaPilotHull_candidate (q : Real) :
    CandidateHull (paperScalingUnits (l := l))
      (paperThetaPilotHull (l := l) q) :=
  holomorphicHull_candidateHull

/-- The actual real q_v from the bad base family. -/
noncomputable def paperBaseQReal (b : Bad (nativePlaceSelection T)) : Real :=
  ‖(baseQ T b).q‖

theorem paperBaseQReal_pos (b : Bad (nativePlaceSelection T)) :
    0 < paperBaseQReal T b :=
  norm_pos_iff.mpr (baseQ T b).q_ne_zero

/-- The actual possible-image union at a bad place b. -/
noncomputable def paperBadPossibleImageSet
    (b : Bad (nativePlaceSelection T)) : Set (PaperThetaPilotPoint (l := l)) :=
  paperPossibleImageSet (l := l) (paperBaseQReal T b)

/-- The actual holomorphic hull at a bad place b. -/
noncomputable def paperBadThetaPilotHull
    (b : Bad (nativePlaceSelection T)) : Submonoid (PaperThetaPilotPoint (l := l)) :=
  paperThetaPilotHull (l := l) (paperBaseQReal T b)

/-- The actual F_l^x procession average of the theta log-values for one bad
place. -/
noncomputable def paperBadProcessionThetaLogVolume
    (b : Bad (nativePlaceSelection T)) : Real :=
  (Fintype.card (PaperThetaPilotCarrier (l := l)) : Real)⁻¹ *
    ∑ j : PaperThetaPilotCarrier (l := l),
      Real.log (paperThetaValue (l := l) (paperBaseQReal T b) j)

/-- The actual global F_l^x procession theta-log candidate over V_bad. -/
noncomputable def globalPaperProcessionThetaLogVolume : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    paperBadProcessionThetaLogVolume T b

end LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual

end
