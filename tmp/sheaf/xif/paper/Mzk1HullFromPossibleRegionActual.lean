/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual

/-! A519/A521: Theta-pilot hull = holomorphic hull of the possible images.

Paper structure of Cor 3.12 (xi-e containment + log-volume monotonicity):
  q-pilot possible image ⊆ Theta-pilot hull  =>  logVol(q region) <= logVol(hull)
where the Theta-pilot hull is the least lambda-O hull of the possible images.
This file constructs that hull on the actual C3 block from the LANA possibleRegion
layer (possible images as `MRRep.possibleRegion`) pushed into the actual tensor
block, and proves the inclusion/log-volume monotonicity lemmas.  It also records
the consistency with S3137 (thetaPilotHull = actual tensor region).

No comparison value is asserted; the remaining input is the image-set
containment (xi-e), which is exactly the possible-images containment of Thm 3.11. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HullFromPossibleRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open Iut.Multiradial
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

universe u v w w'

/-! ## 1. Generic possible images -/

variable {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]

/-- The possible images of a representative of the raw output (xi-e level). -/
def possibleImageSet (raw : RawOutput.{u, v, w} G A) {P : G} {X : Type*}
    (reg : raw.F.obj P -> Set X) (x : raw.F.obj P) : Set X :=
  MRRep.possibleRegion (R := raw) reg (MRRep.mk (R := raw) x)

theorem region_subset_possibleImageSet (raw : RawOutput.{u, v, w} G A) {P : G}
    {X : Type*} (reg : raw.F.obj P -> Set X) (x : raw.F.obj P) :
    reg x <= possibleImageSet raw reg x :=
  MRRep.reg_subset_possibleRegion reg x

/-- Monotonicity of possible images in the region construction. -/
theorem possibleImageSet_mono (raw : RawOutput.{u, v, w} G A) {P : G}
    {X : Type*} {reg1 reg2 : raw.F.obj P -> Set X}
    (h : forall y, reg1 y <= reg2 y) (x : raw.F.obj P) :
    possibleImageSet raw reg1 x <= possibleImageSet raw reg2 x := by
  intro z hz
  rw [possibleImageSet, MRRep.possibleRegion] at hz ⊢
  simp only [Set.mem_iUnion] at hz ⊢
  rcases hz with ⟨y, hy, hzy⟩
  exact ⟨y, hy, h y hzy⟩

/-! ## 2. The hull of possible images on the actual C3 block -/

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

What is the possible-image set on the actual C3 block - it is encoded by a
 -/
realization from the raw-output fiber into the actual tensor block. -/
def blockImageSet {X : Type*} (realize : X -> C3LogShellTensorBlock C3)
    (S : Set X) : Set (C3LogShellTensorBlock C3) :=
  realize '' S

/-- The Theta-pilot hull as the least lambda-O hull of the possible images:
the possible images are first realized in the actual tensor block, then the
actual holomorphic hull (C3LogShellTensorHolomorphicHullActual) is taken. -/
def hullFromPossibleRegion (raw : RawOutput.{u, v, w} G A) {P : G} {X : Type*}
    (reg : raw.F.obj P -> Set X) (x : raw.F.obj P)
    (realize : X -> C3LogShellTensorBlock C3) :
    Set (C3LogShellTensorBlock C3) :=
  actualHolomorphicHull C3 (blockImageSet C3 realize (possibleImageSet raw reg x))

/-- The possible images are contained in their hull. -/
theorem possibleImageSet_subset_hullFromPossibleRegion
    (raw : RawOutput.{u, v, w} G A) {P : G} {X : Type*}
    (reg : raw.F.obj P -> Set X) (x : raw.F.obj P)
    (realize : X -> C3LogShellTensorBlock C3) :
    blockImageSet C3 realize (possibleImageSet raw reg x) <=
      hullFromPossibleRegion C3 raw reg x realize :=
  actualRegion_subset_hull C3 (blockImageSet C3 realize (possibleImageSet raw reg x))

/-- Hull monotonicity in the possible-image set. -/
theorem hullFromPossibleRegion_mono
    (raw : RawOutput.{u, v, w} G A) {P : G} {X : Type*}
    {reg1 reg2 : raw.F.obj P -> Set X} (h : forall y, reg1 y <= reg2 y)
    (x : raw.F.obj P) (realize : X -> C3LogShellTensorBlock C3) :
    hullFromPossibleRegion C3 raw reg1 x realize <=
      hullFromPossibleRegion C3 raw reg2 x realize :=
  actualHolomorphicHull_monotone C3
    (blockImageSet C3 realize (possibleImageSet raw reg1 x))
    (blockImageSet C3 realize (possibleImageSet raw reg2 x))
    (fun z hz => by
      rcases hz with ⟨y, hy, rfl⟩
      exact ⟨y, possibleImageSet_mono raw h x hy, rfl⟩)

/-- If the possible images lie in the actual C3 tensor region, then the hull of
the possible images lies in the actual region: the actual region is itself a
lambda-O candidate hull (1 * O). -/
theorem hullFromPossibleRegion_subset_actualRegion
    (raw : RawOutput.{u, v, w} G A) {P : G} {X : Type*}
    (reg : raw.F.obj P -> Set X) (x : raw.F.obj P)
    (realize : X -> C3LogShellTensorBlock C3)
    (hImg : blockImageSet C3 realize (possibleImageSet raw reg x) <=
      actualC3LogShellTensorRegion C3) :
    hullFromPossibleRegion C3 raw reg x realize <=
      actualC3LogShellTensorRegion C3 :=
  actualHolomorphicHull_subset_candidate C3 _ _
    (actualUnitRegion_mem_candidateHulls C3)
    (by simpa [actualUnitRegion] using hImg)

/-! ## 3. Log-volume monotonicity on the actual C3 block -/

theorem actualRegion_measure_lt_top :
    (actualC3LogShellTensorHaar C3) (actualC3LogShellTensorRegion C3) < ⊤ :=
  c3TensorRegion_measure_lt_top (C3 := C3)

/-- Inclusion of the hull in the actual region gives the Haar log-volume
inequality (the monotonicity step of xi-f). -/
theorem hullFromPossibleRegion_logVolume_le_actualRegion
    (raw : RawOutput.{u, v, w} G A) {P : G} {X : Type*}
    (reg : raw.F.obj P -> Set X) (x : raw.F.obj P)
    (realize : X -> C3LogShellTensorBlock C3)
    (hImg : blockImageSet C3 realize (possibleImageSet raw reg x) <=
      actualC3LogShellTensorRegion C3) :
    haarLogVolume (actualC3LogShellTensorHaar C3)
        (hullFromPossibleRegion C3 raw reg x realize) <=
      haarLogVolume (actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3) :=
  haarLogVolume_mono (hullFromPossibleRegion_subset_actualRegion C3 raw reg x realize hImg)

/-- Real (finite) form of the same monotonicity, matching the S3137 theta-pilot
hull readout `thetaPilotHullLogVolumeReal C3`. -/
theorem hullFromPossibleRegion_realLogVolume_le_thetaPilotHull
    (raw : RawOutput.{u, v, w} G A) {P : G} {X : Type*}
    (reg : raw.F.obj P -> Set X) (x : raw.F.obj P)
    (realize : X -> C3LogShellTensorBlock C3)
    (hImg : blockImageSet C3 realize (possibleImageSet raw reg x) <=
      actualC3LogShellTensorRegion C3)
    (hpos : 0 < (actualC3LogShellTensorHaar C3)
      (hullFromPossibleRegion C3 raw reg x realize)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        (hullFromPossibleRegion C3 raw reg x realize)).toReal <=
      thetaPilotHullLogVolumeReal C3 :=
   by
  rw [thetaPilotHullLogVolumeReal_eq_regionLogVolume]
  have hle := hullFromPossibleRegion_logVolume_le_actualRegion C3 raw reg x realize hImg
  have hfin : (actualC3LogShellTensorHaar C3)
      (actualC3LogShellTensorRegion C3) < ⊤ := actualRegion_measure_lt_top C3
  have hmono : (actualC3LogShellTensorHaar C3)
      (hullFromPossibleRegion C3 raw reg x realize) <= (actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3) :=
    hullFromPossibleRegion_subset_actualRegion C3 raw reg x realize hImg
  have hreal := ENNReal.toReal_mono hfin.ne hmono
  exact Real.log_le_log hpos hreal

/-! ## 4. Consistency with S3137: thetaPilotHull = actual tensor region -/

theorem s3137_hull_eq_actualRegion :
    thetaPilotHull C3 = actualC3LogShellTensorRegion C3 :=
  thetaPilotHull_eq_region (C3 := C3)

theorem s3137_thetaHullLogVolume_eq_actualRegion :
    thetaPilotHullLogVolumeReal C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_regionLogVolume (C3 := C3)

/-- The hull-from-possible-images object on the actual C3 data. -/
structure HullFromPossibleRegionObject
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  hull : Set (C3LogShellTensorBlock C3)
  hull_eq : hull = thetaPilotHull C3
  hull_subset_region : hull <= actualC3LogShellTensorRegion C3
  readout : Real
  readout_eq : readout = thetaPilotHullLogVolumeReal C3

noncomputable def hullFromPossibleRegionObject :
    HullFromPossibleRegionObject C3 where
  hull := thetaPilotHull C3
  hull_eq := rfl
  hull_subset_region := by rw [thetaPilotHull_eq_region]
  readout := thetaPilotHullLogVolumeReal C3
  readout_eq := rfl

theorem hullFromPossibleRegionObject_constructed :
    (hullFromPossibleRegionObject C3).hull = thetaPilotHull C3 ∧
    (hullFromPossibleRegionObject C3).readout =
      thetaPilotHullLogVolumeReal C3 := by
  refine ⟨rfl, rfl⟩

/-! ## 5. The xi-f formal step shape -/

def regionLe (thetaLog : Real) : Set Real := Set.Iic thetaLog

theorem regionLe_mem_iff {thetaLog qLog : Real} :
    qLog ∈ regionLe thetaLog <-> qLog <= thetaLog := Iff.rfl

theorem xi_f_formal_step {thetaLog qLog : Real}
    (h : qLog ∈ regionLe thetaLog) : qLog <= thetaLog := h

end LeanFormal.IUT.XiFPaper.Mzk1HullFromPossibleRegionActual