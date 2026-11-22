import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeometryReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealEdgeNormalizationReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealEdgeNormalizationDichotomy
import Mathlib

/-!
# O4 constructed hull: actual theta packet and via-images identity

From the actual FiniteThetaPacket (whose scale is the Gaussian special value,
scale_eq = realThetaValue q j), the actual possible theta-pilot image set, and
the actual source holomorphic hull, this file constructs the value-layer
via-images target

  sourceHullVolume = imageVolume

and proves:
- it is equivalent to the single edge inequality hull <= image;
- it is equivalent to nonpositivity of the log-degree on the entire hull;
- a decisive no-go: any positive-log-degree hull point makes the identity fail.

No arbitrary hull or readout is introduced.
-/

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory

namespace LeanFormal.IUT.N8Closure.O4ConstructedHull

universe ua uv upi umon ui u v w

variable {l : PrimeGeFive}

/-! ## 1. Actual Gaussian theta packet -/

/-- Actual finite theta packet with q-parameter q. -/
def gaussianThetaPacket (q : ℝ) (hq : 0 < q) : FiniteThetaPacket l :=
  FiniteThetaPacket.ofQ (l := l) q hq

/-- Its scale is the actual real theta special value. -/
theorem gaussianThetaPacket_scale (q : ℝ) (hq : 0 < q)
    (j : SignedLabel l.value) :
    (gaussianThetaPacket (l := l) q hq).scale j =
      realThetaValue q j.1 :=
  rfl

/-- Logarithmic Gaussian form: log scale = j^2 * log q. -/
theorem gaussianThetaPacket_log_scale (q : ℝ) (hq : 0 < q)
    (j : SignedLabel l.value) :
    Real.log ((gaussianThetaPacket (l := l) q hq).scale j) =
      (gaussExponent j.1).toNat * Real.log q :=
  FiniteThetaPacket.log_scale (packet := gaussianThetaPacket (l := l) q hq) j

/-- Actual source theta packet from the source theater. -/
def sourceThetaPacket {V : Type uv} (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n m : ℤ) : FiniteThetaPacket l :=
  (I.theaterAt n m).thetaPacket

theorem sourceThetaPacket_scale {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : ℤ)
    (j : SignedLabel l.value) :
    (sourceThetaPacket (l := l) I n m).scale j = I.thetaValueAt n m j :=
  rfl

/-! ## 2. Actual possible image set, holomorphic hull, volumes -/

variable {V : Type uv} (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- Actual possible theta-pilot image set. -/
def possibleImageSet : Set (I.ThetaPilotPoint v) :=
  I.possibleThetaPilotImageSet v R n

/-- Actual source holomorphic hull. -/
def holomorphicHullActual : Set (I.ThetaPilotPoint v) :=
  I.sourceHolomorphicHull v R n

/-- Actual hull volume. -/
def hullVolume : ENNReal := I.sourceHullVolume v R n

/-- Actual image-union volume. -/
def imageVolume : ENNReal := I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)

/-- Via-images value-layer identity. -/
def ViaImagesIdentity : Prop := hullVolume I v R n = imageVolume I v R n

/-- The via-images identity is exactly the remaining edge inequality. -/
theorem viaImagesIdentity_iff_edge :
    ViaImagesIdentity I v R n ↔
      hullVolume I v R n ≤ imageVolume I v R n := by
  unfold ViaImagesIdentity hullVolume imageVolume
  exact I.sourceHullVolume_eq_imageVolume_iff v R n

/-- Exact value-layer characterization: the via-images identity holds iff every
hull point has nonpositive source log-degree. -/
theorem viaImagesIdentity_iff_hullLogDegree_nonpos :
    ViaImagesIdentity I v R n ↔
      ∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourceLocalLogDegree v z ≤ 0 := by
  rw [viaImagesIdentity_iff_edge]
  unfold hullVolume imageVolume
  change I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n ↔
    ∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
      I.sourceLocalLogDegree v z ≤ 0
  rw [I.sourceHullVolume_le_imageVolume_iff_hull_logDegree_nonpos]

/-- Decisive no-go / actual counterexample schema: any positive-log-degree hull
point makes the via-images equality fail. -/
theorem not_viaImagesIdentity_of_hullLogDegree_pos
    (h : ∃ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
      0 < I.sourceLocalLogDegree v z) :
    ¬ ViaImagesIdentity I v R n := by
  intro hEq
  have hnonpos :=
    (viaImagesIdentity_iff_hullLogDegree_nonpos I v R n).mp hEq
  obtain ⟨z, hz, hpos⟩ := h
  exact (not_le_of_gt hpos) (hnonpos z hz)

end LeanFormal.IUT.N8Closure.O4ConstructedHull