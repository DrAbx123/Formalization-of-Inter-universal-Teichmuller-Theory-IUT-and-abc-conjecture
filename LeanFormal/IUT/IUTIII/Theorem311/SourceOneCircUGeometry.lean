/-
# P3: the `1,circ U` geometry interface layer (model level)

Source anchor: IUT III, Corollary 3.12 proof, Step (xi) (corpus lines
10359--10416); Remark 3.9.5, (i), (ii) (corpus lines 7653--7750).  The paper's
object is the finite family

  `1,circ U_{j,vQ}`  for  `j in |Fl|`, `vQ in VQ`,

a union of possible images of the Theta-pilot object inside the tensor packet
`IQ(S+-_{j+1}; 1,circ D^vdash_{vQ})`, together with its holomorphic hull.  The
[easily verified] compactness of the `1,circ U_{j,vQ}` and the definition of the
log-volume give the finiteness of `-|log Theta|`.

This file implements the **P3 data/geometry layer** identified in
`logs/coordination/gaussian-processions-gap-20261017.md`, section 7.2, and the
third item of plan A in section 8.1.  It provides:

* `OneCircUIndexFamily`: the finite index family `|Fl| x VQ`, with `|Fl|` the
  finite theta-pilot carrier (`lPlus = lStar + 1` labels) and `VQ` an arbitrary
  finite nonempty type;
* `OneCircUGeometry`: a normed real vector-space model of the ambient
  `O`-module carrier, a finite family of compact local images, the region
  `oneCircU` defined as their finite union, the closed convex hull `hull`, a
  unit region `O`, a scaled region `lambda . O`, and the geometric hypotheses
  (convexity of `O`, closedness/boundedness of `lambda . O`) from which the
  paper-shaped conclusions are proved;
* proofs of `oneCircU_isCompact`, `hull_subset_scaledUnitRegion`,
  `hull_logVolume_lt_top`, and the realization of `IQHullLogVolumeInterface`;
* a concrete nonempty, non-`univ` model on
  `(Fl x VQ) -> Real`: `localImageCube` is a closed cube of radius `1/4`
  around a grid center in the unit cube, `oneCircU` is the finite union of
  these cubes, `O` is the unit cube, and `lambda = 2`;
* a conditional transport theorem from a geometric identification with the
  actual value carrier to the source hull volume.

## Model boundary (explicit)

This is **not** the paper's `1,circ U_{j,vQ}`.  The actual carrier
`IQ(S+-_{j+1}; 1,circ D^vdash_{vQ})` is not constructed here; there is no
LGP-monoid, no Theta-pilot object, no Ind1/Ind2/Ind3, no arithmetic
holomorphic structure, no Haar measure, and no procession average.  The
ambient space is a finite product of copies of `Real`; the `O`-module
structure is represented by the normed real vector-space model and the unit
cube; `localImageCube` is a geometric stand-in for a possible theta-pilot
image; `hull` is the topological closed convex hull, not the arithmetic
holomorphic hull.  The index `|Fl|` is identified with the existing finite
theta-pilot carrier `Fin (lStar + 1)`; `VQ` is an additional finite type.
The scaling `lambda = 2` is a chosen model parameter, not a source-derived
quantity.  Therefore this file closes the **model-level P3 shape**, not the
paper-level N6 compactness statement.  The conditional source transport below
states exactly what an identification with the actual carrier would have to
supply.
-/

import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.IUTIII.Theorem311.HullLambdaDilationLayer

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace LeanFormal.IUT

noncomputable section

universe uX uFl uVQ

/-! ## 1. The finite index family `|Fl| x VQ` -/

/-- The finite index family of the paper: `|Fl|` is the finite set of
theta-pilot procession labels (`lPlus = lStar + 1` elements) and `VQ` is the
set of valuations of `Q`.  Both are finite and nonempty. -/
structure OneCircUIndexFamily where
  /-- The finite label set `|Fl|`. -/
  Fl : Type uFl
  [fintypeFl : Fintype Fl]
  [nonemptyFl : Nonempty Fl]
  /-- The finite valuation set `VQ`. -/
  VQ : Type uVQ
  [fintypeVQ : Fintype VQ]
  [nonemptyVQ : Nonempty VQ]

namespace OneCircUIndexFamily

attribute [instance] fintypeFl fintypeVQ

/-- The product index family is finite, as used for the finite union defining
`1,circ U`. -/
instance fintypeProd (F : OneCircUIndexFamily) : Fintype (F.Fl × F.VQ) :=
  inferInstance

/-- The product index family is nonempty. -/
theorem nonemptyProd (F : OneCircUIndexFamily) : Nonempty (F.Fl × F.VQ) :=
  ⟨(Classical.choice F.nonemptyFl, Classical.choice F.nonemptyVQ)⟩

/-- The cardinality of the product index family. -/
theorem card_prod (F : OneCircUIndexFamily) :
    Fintype.card (F.Fl × F.VQ) = Fintype.card F.Fl * Fintype.card F.VQ :=
  Fintype.card_prod F.Fl F.VQ

end OneCircUIndexFamily

/-! ## 2. The abstract geometry interface -/

/-- The P3 geometry of `1,circ U` at the model level: a normed real
vector-space carrier, a finite family of compact local images, a convex unit
region `O`, a closed bounded scaled region `lambda . O`, and the containment
`O subseteq lambda . O`.  The region `oneCircU` and the hull are definitions
below, not fields; the paper-shaped conclusions are theorems. -/
structure OneCircUGeometry (X : Type uX) [NormedAddCommGroup X]
    [NormedSpace ℝ X] extends OneCircUIndexFamily.{uFl, uVQ} where
  /-- The possible image of the theta-pilot object at an index `(j, vQ)`. -/
  localImage : Fl × VQ → Set X
  /-- Each possible image is compact, as in the [easily verified] compactness
  of `1,circ U_{j,vQ}`. -/
  localImage_compact : ∀ p, IsCompact (localImage p)
  /-- Each possible image is nonempty (the theta-pilot image is a genuine
  region, not the empty set). -/
  localImage_nonempty : ∀ p, (localImage p).Nonempty
  /-- The unit region `O` (the role of the ring-of-integers/log-shell region). -/
  unitRegion : Set X
  /-- The unit region is convex; this is the convexity of the model `O`. -/
  unitRegion_convex : Convex ℝ unitRegion
  /-- Every local image lies in the unit region. -/
  localImage_subset_unitRegion : ∀ p, localImage p ⊆ unitRegion
  /-- The scaled region `lambda . O`. -/
  scaledUnitRegion : Set X
  /-- The scaled region is closed, so the closure of the hull stays inside it. -/
  scaledUnitRegion_closed : IsClosed scaledUnitRegion
  /-- `O subseteq lambda . O` for the chosen scaling. -/
  unitRegion_subset_scaledUnitRegion : unitRegion ⊆ scaledUnitRegion
  /-- The scaled region is bounded, so its log-volume is finite. -/
  scaledUnitRegion_bounded : Bornology.IsBounded scaledUnitRegion

namespace OneCircUGeometry

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The region `1,circ U`: the finite union of the possible images over
`|Fl| x VQ`.  This is a definition, not an interface field. -/
def oneCircU (G : OneCircUGeometry X) : Set X :=
  ⋃ p : G.Fl × G.VQ, G.localImage p

/-- The holomorphic hull slot at the model level: the topological closed convex
hull of `1,circ U`.  This is a definition, not an interface field. -/
def hull (G : OneCircUGeometry X) : Set X :=
  closure (convexHull ℝ G.oneCircU)

theorem mem_oneCircU_iff (G : OneCircUGeometry X) {x : X} :
    x ∈ G.oneCircU ↔ ∃ p : G.Fl × G.VQ, x ∈ G.localImage p := by
  simp [oneCircU]

/-- `1,circ U` is nonempty: the index family is nonempty and each local image
is nonempty. -/
theorem oneCircU_nonempty (G : OneCircUGeometry X) : G.oneCircU.Nonempty := by
  obtain ⟨p⟩ := G.nonemptyProd
  obtain ⟨x, hx⟩ := G.localImage_nonempty p
  exact ⟨x, (G.mem_oneCircU_iff).mpr ⟨p, hx⟩⟩

/-- **Compactness of `1,circ U`**: a finite union of compact local images. -/
theorem oneCircU_isCompact (G : OneCircUGeometry X) : IsCompact G.oneCircU := by
  letI : Fintype G.Fl := G.fintypeFl
  letI : Fintype G.VQ := G.fintypeVQ
  simpa [oneCircU] using
    (isCompact_iUnion (fun p : G.Fl × G.VQ => G.localImage_compact p))

/-- The local images lie in the unit region. -/
theorem oneCircU_subset_unitRegion (G : OneCircUGeometry X) :
    G.oneCircU ⊆ G.unitRegion := by
  intro x hx
  obtain ⟨p, hp⟩ := (G.mem_oneCircU_iff).mp hx
  exact G.localImage_subset_unitRegion p hp

/-- `P subseteq phi(P)`: the region is contained in its hull. -/
theorem oneCircU_subset_hull (G : OneCircUGeometry X) :
    G.oneCircU ⊆ G.hull :=
  (subset_convexHull ℝ G.oneCircU).trans subset_closure

/-- **The paper-shaped containment `hull subseteq lambda . O`**, proved from
the convexity of `O`, the containment of the local images in `O`, and the
closedness of `lambda . O`.  No field of the structure states this conclusion. -/
theorem hull_subset_scaledUnitRegion (G : OneCircUGeometry X) :
    G.hull ⊆ G.scaledUnitRegion := by
  apply closure_minimal
  · exact (convexHull_min (fun x hx => G.oneCircU_subset_unitRegion hx)
      G.unitRegion_convex).trans G.unitRegion_subset_scaledUnitRegion
  · exact G.scaledUnitRegion_closed

/-- The hull is closed (the closure of a convex hull). -/
theorem hull_isClosed (G : OneCircUGeometry X) : IsClosed G.hull :=
  isClosed_closure

/-- The hull is contained in the closed scaled region and is therefore
bounded. -/
theorem hull_bounded (G : OneCircUGeometry X) : Bornology.IsBounded G.hull :=
  G.scaledUnitRegion_bounded.subset G.hull_subset_scaledUnitRegion
end OneCircUGeometry

/-! ## 3. The log-volume functional and its finiteness -/

/-- The model log-volume of a region: the supremum of the point log-degrees
`ENNReal.ofReal ‖x‖` over the region.  This is the same `iSup`-of-point-volumes
shape as the source `sourceSetVolume`, with the norm playing the role of the
log-degree.  It is monotone under inclusion. -/
def modelLogVolume {X : Type uX} [Norm X] (S : Set X) : ENNReal :=
  ⨆ x ∈ S, ENNReal.ofReal ‖x‖

theorem modelLogVolume_mono {X : Type uX} [Norm X] {S T : Set X}
    (hST : S ⊆ T) : modelLogVolume S ≤ modelLogVolume T := by
  unfold modelLogVolume
  refine iSup_le fun x => iSup_le fun hx => ?_
  exact le_iSup_of_le x (le_iSup_of_le (hST hx) le_rfl)

theorem modelLogVolume_le_of_forall_norm_le {X : Type uX} [Norm X] {S : Set X}
    {C : ℝ} (h : ∀ x ∈ S, ‖x‖ ≤ C) :
    modelLogVolume S ≤ ENNReal.ofReal C := by
  unfold modelLogVolume
  exact iSup_le fun x => iSup_le fun hx => ENNReal.ofReal_le_ofReal (h x hx)

namespace OneCircUGeometry

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The scaled region has finite log-volume: it is bounded. -/
theorem scaledUnitRegion_logVolume_lt_top (G : OneCircUGeometry X) :
    modelLogVolume G.scaledUnitRegion < ⊤ := by
  obtain ⟨C, hC⟩ := G.scaledUnitRegion_bounded.exists_norm_le
  exact lt_of_le_of_lt (modelLogVolume_le_of_forall_norm_le hC)
    ENNReal.ofReal_lt_top

/-- **Finiteness of the hull log-volume**: the hull lies in the bounded scaled
region.  This is the model-level shape of the paper's conclusion that
`-|log Theta|` is finite. -/
theorem hull_logVolume_lt_top (G : OneCircUGeometry X) :
    modelLogVolume G.hull < ⊤ :=
  lt_of_le_of_lt (modelLogVolume_mono G.hull_subset_scaledUnitRegion)
    G.scaledUnitRegion_logVolume_lt_top

/-- The region `1,circ U` also has finite log-volume. -/
theorem oneCircU_logVolume_lt_top (G : OneCircUGeometry X) :
    modelLogVolume G.oneCircU < ⊤ :=
  lt_of_le_of_lt
    (modelLogVolume_mono
      (G.oneCircU_subset_unitRegion.trans G.unitRegion_subset_scaledUnitRegion))
    G.scaledUnitRegion_logVolume_lt_top

/-- The P3 geometry realizes the `IQHullLogVolumeInterface` consumed by the
Step-XI certificate layer.  The `scaleShift` is the identity because the
scaling has been absorbed into `scaledUnitRegion` (the normalization
convention used by `sourceOModuleCompactness_haarData`); the content is the
proved hull containment and the proved finiteness. -/
def toIQHullLogVolumeInterface (G : OneCircUGeometry X) :
    IQHullLogVolumeInterface X where
  imageSet := G.oneCircU
  hull := G.hull
  imageSet_subset_hull := G.oneCircU_subset_hull
  logVolume := modelLogVolume
  logVolume_mono := fun hST => modelLogVolume_mono hST
  unitRegion := G.scaledUnitRegion
  scaleShift := id
  hull_subset_scaleShift := by
    intro x hx
    exact ⟨x, G.hull_subset_scaledUnitRegion hx, rfl⟩
  unitRegion_logVolume_lt_top := G.scaledUnitRegion_logVolume_lt_top
  scaleShift_unitRegion_logVolume_le := by simp

/-- The interface's hull is the geometric hull and its log-volume is the model
log-volume. -/
@[simp] theorem toIQHullLogVolumeInterface_hull (G : OneCircUGeometry X) :
    (G.toIQHullLogVolumeInterface).hull = G.hull := rfl

/-- The interface's finiteness theorem is exactly the hull finiteness theorem. -/
theorem toIQHullLogVolumeInterface_hull_logVolume_lt_top
    (G : OneCircUGeometry X) :
    (G.toIQHullLogVolumeInterface).logVolume
      (G.toIQHullLogVolumeInterface).hull < ⊤ :=
  (G.toIQHullLogVolumeInterface).hull_logVolume_lt_top

/-- The interface's lower-bound transfer fires on the model data. -/
theorem toIQHullLogVolumeInterface_lower_bound_and_finiteness
    (G : OneCircUGeometry X) {lowerBound : ENNReal}
    (h : lowerBound ≤ modelLogVolume G.oneCircU) :
    lowerBound ≤ modelLogVolume G.hull ∧ modelLogVolume G.hull < ⊤ :=
  (G.toIQHullLogVolumeInterface).lower_bound_and_finiteness h

end OneCircUGeometry

/-! ## 4. The concrete real tensor-cube model -/

/-- `|Fl|` as the finite theta-pilot carrier `Fin (lStar + 1)`; its cardinality
is `lPlus = lStar + 1`, matching IUT I's `l± = |Fl|`. -/
abbrev FlIndex (l : PrimeGeFive) : Type :=
  Theorem311Source.OriginalInput.ThetaPilotCarrier l

instance flIndexFintype (l : PrimeGeFive) : Fintype (FlIndex l) :=
  inferInstanceAs (Fintype (Fin (lStar l.value + 1)))

instance flIndexNonempty (l : PrimeGeFive) : Nonempty (FlIndex l) :=
  ⟨⟨0, Nat.succ_pos (lStar l.value)⟩⟩

theorem flIndex_card (l : PrimeGeFive) :
    Fintype.card (FlIndex l) = lStar l.value + 1 := by
  change Fintype.card (Fin (lStar l.value + 1)) = lStar l.value + 1
  exact Fintype.card_fin _

section RealTensorModel

variable (l : PrimeGeFive) (VQ : Type uVQ)

/-- The concrete carrier model: one real coordinate for each index
`(j, vQ) in |Fl| x VQ`.  This is a finite product of copies of `Real`, with the
product normed real vector-space structure. -/
abbrev RealTensorCarrier : Type uVQ :=
  (FlIndex l × VQ) → ℝ

/-- The unit region `O`: the unit cube in the product carrier. -/
def unitCube : Set (RealTensorCarrier l VQ) :=
  HullLambdaDilation.cubeDilation (fun _ : FlIndex l × VQ => (1 : WithTop ℝ))

theorem mem_unitCube_iff {x : RealTensorCarrier l VQ} :
    x ∈ unitCube l VQ ↔ ∀ p : FlIndex l × VQ, |x p| ≤ 1 := by
  simp [unitCube, HullLambdaDilation.cubeDilation]

theorem unitCube_eq_pi_Icc :
    unitCube l VQ =
      Set.univ.pi (fun _ : FlIndex l × VQ => Set.Icc (-1 : ℝ) 1) := by
  simpa [unitCube] using
    (HullLambdaDilation.cubeDilation_eq_pi_Icc
      (ι := FlIndex l × VQ) (fun _ => (1 : ℝ)))

theorem convex_unitCube : Convex ℝ (unitCube l VQ) := by
  rw [unitCube_eq_pi_Icc]
  exact convex_pi (s := Set.univ)
    (t := fun _ : FlIndex l × VQ => Set.Icc (-1 : ℝ) 1)
    (fun _ _ => convex_Icc (-1 : ℝ) 1)

/-- The scaled region `lambda . O`. -/
def scaledCube (lam : ℝ) : Set (RealTensorCarrier l VQ) :=
  HullLambdaDilation.cubeDilation (fun _ : FlIndex l × VQ => (lam : WithTop ℝ))

theorem mem_scaledCube_iff {lam : ℝ} {x : RealTensorCarrier l VQ} :
    x ∈ scaledCube l VQ lam ↔ ∀ p : FlIndex l × VQ, |x p| ≤ lam := by
  simp [scaledCube, HullLambdaDilation.cubeDilation]

theorem isCompact_scaledCube (lam : ℝ) : IsCompact (scaledCube l VQ lam) := by
  simpa [scaledCube] using
    (HullLambdaDilation.isCompact_cubeDilation
      (ι := FlIndex l × VQ) (fun _ => lam))

theorem unitCube_subset_scaledCube_two :
    unitCube l VQ ⊆ scaledCube l VQ 2 := by
  intro x hx
  rw [mem_scaledCube_iff]
  intro p
  have h1 : |x p| ≤ 1 := (mem_unitCube_iff (l := l) (VQ := VQ)).mp hx p
  linarith

/-- The grid center of the local cube at an index `p`: `1/2` in the `p`
coordinate and `0` elsewhere.  It lies in the unit cube. -/
noncomputable def gridCenter (p : FlIndex l × VQ) : RealTensorCarrier l VQ := by
  classical
  exact fun q => if q = p then (1 / 2 : ℝ) else 0

theorem abs_gridCenter_le_half (p q : FlIndex l × VQ) :
    |gridCenter l VQ p q| ≤ (1 / 2 : ℝ) := by
  classical
  by_cases h : q = p <;> simp [gridCenter, h]

/-- The local possible-image model: a closed cube of radius `1/4` around the
grid center.  It is a geometric stand-in for one possible theta-pilot image. -/
def localImageCube (p : FlIndex l × VQ) : Set (RealTensorCarrier l VQ) :=
  {x | ∀ q : FlIndex l × VQ,
    |x q - gridCenter l VQ p q| ≤ (1 / 4 : ℝ)}

theorem localImageCube_eq_pi_Icc (p : FlIndex l × VQ) :
    localImageCube l VQ p =
      Set.univ.pi (fun q : FlIndex l × VQ =>
        Set.Icc (gridCenter l VQ p q - (1 / 4 : ℝ))
          (gridCenter l VQ p q + (1 / 4 : ℝ))) := by
  ext x
  simp only [localImageCube, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
  constructor
  · intro h q
    have hq := abs_le.mp (h q)
    constructor <;> linarith
  · intro h q
    exact abs_le.mpr ⟨by linarith [(h q).1], by linarith [(h q).2]⟩

theorem isCompact_localImageCube (p : FlIndex l × VQ) :
    IsCompact (localImageCube l VQ p) := by
  rw [localImageCube_eq_pi_Icc]
  exact isCompact_univ_pi fun q => isCompact_Icc

theorem gridCenter_mem_localImageCube (p : FlIndex l × VQ) :
    gridCenter l VQ p ∈ localImageCube l VQ p := by
  intro q
  simp

theorem localImageCube_nonempty (p : FlIndex l × VQ) :
    (localImageCube l VQ p).Nonempty :=
  ⟨gridCenter l VQ p, gridCenter_mem_localImageCube l VQ p⟩

theorem localImageCube_subset_unitCube (p : FlIndex l × VQ) :
    localImageCube l VQ p ⊆ unitCube l VQ := by
  intro x hx
  rw [mem_unitCube_iff]
  intro q
  have hq : |x q - gridCenter l VQ p q| ≤ (1 / 4 : ℝ) := hx q
  have hc : |gridCenter l VQ p q| ≤ (1 / 2 : ℝ) := abs_gridCenter_le_half l VQ p q
  have htri : |x q| ≤ |x q - gridCenter l VQ p q| + |gridCenter l VQ p q| := by
    calc
      |x q| = |(x q - gridCenter l VQ p q) + gridCenter l VQ p q| := by
        rw [sub_add_cancel]
      _ ≤ |x q - gridCenter l VQ p q| + |gridCenter l VQ p q| := abs_add_le _ _
  linarith

variable [Fintype VQ] [Nonempty VQ]

/-- The concrete P3 geometry: finite index family `|Fl| x VQ`, local cubes,
the unit cube as `O`, and `lambda = 2`. -/
def realTensorGeometry : OneCircUGeometry (RealTensorCarrier l VQ) where
  Fl := FlIndex l
  fintypeFl := flIndexFintype l
  nonemptyFl := flIndexNonempty l
  VQ := VQ
  fintypeVQ := inferInstance
  nonemptyVQ := ‹Nonempty VQ›
  localImage := localImageCube l VQ
  localImage_compact := isCompact_localImageCube l VQ
  localImage_nonempty := localImageCube_nonempty l VQ
  unitRegion := unitCube l VQ
  unitRegion_convex := convex_unitCube l VQ
  localImage_subset_unitRegion := localImageCube_subset_unitCube l VQ
  scaledUnitRegion := scaledCube l VQ 2
  scaledUnitRegion_closed := (isCompact_scaledCube l VQ 2).isClosed
  unitRegion_subset_scaledUnitRegion := unitCube_subset_scaledCube_two l VQ
  scaledUnitRegion_bounded := (isCompact_scaledCube l VQ 2).isBounded

theorem realTensor_index_card :
    Fintype.card (FlIndex l × VQ) = (lStar l.value + 1) * Fintype.card VQ := by
  rw [Fintype.card_prod, flIndex_card]

theorem realTensor_oneCircU_nonempty :
    (realTensorGeometry l VQ).oneCircU.Nonempty :=
  (realTensorGeometry l VQ).oneCircU_nonempty

theorem realTensor_oneCircU_isCompact :
    IsCompact (realTensorGeometry l VQ).oneCircU :=
  (realTensorGeometry l VQ).oneCircU_isCompact

theorem realTensor_hull_subset_scaledCube_two :
    (realTensorGeometry l VQ).hull ⊆ scaledCube l VQ 2 :=
  (realTensorGeometry l VQ).hull_subset_scaledUnitRegion

theorem realTensor_hull_logVolume_lt_top :
    modelLogVolume (realTensorGeometry l VQ).hull < ⊤ :=
  (realTensorGeometry l VQ).hull_logVolume_lt_top

/-- The concrete `1,circ U` is not the whole ambient carrier: the constant
point `2` is outside the unit cube and hence outside the finite union of local
cubes. -/
theorem realTensor_oneCircU_ne_univ :
    ((realTensorGeometry l VQ).oneCircU : Set (RealTensorCarrier l VQ)) ≠ Set.univ := by
  intro h
  let x : RealTensorCarrier l VQ := fun _ => (2 : ℝ)
  have hx : x ∈ (realTensorGeometry l VQ).oneCircU := by
    rw [h]
    exact Set.mem_univ x
  have hxunit : x ∈ unitCube l VQ :=
    (realTensorGeometry l VQ).oneCircU_subset_unitRegion hx
  let p : FlIndex l × VQ :=
    (Classical.choice (flIndexNonempty l), Classical.choice (inferInstance : Nonempty VQ))
  have h2 : |x p| ≤ 1 := (mem_unitCube_iff (l := l) (VQ := VQ)).mp hxunit p
  dsimp [x] at h2
  norm_num at h2

end RealTensorModel

/-! ## 5. Conditional transport to the source hull volume (N7 shape) -/

section SourceTransport

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- If the model carrier is identified with the actual value carrier by an
equivalence that preserves point log-volumes and identifies the model hull
with the source holomorphic hull, then the model's finiteness theorem is the
source hull-volume finiteness statement.  The identification is an explicit
hypothesis; no such identification is constructed here. -/
theorem sourceHullVolume_eq_modelLogVolume_of_equiv {X : Type uX}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : V) (R : I.SourceImageRealization v)
    (n : Theorem311Source.OriginalInput.ThetaPilotCarrier l)
    (G : OneCircUGeometry X) (e : X ≃ I.ThetaPilotPoint v)
    (hpoint : ∀ x : X, I.sourcePointVolume v (e x) = ENNReal.ofReal ‖x‖)
    (hhull : e '' G.hull =
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))) :
    I.sourceHullVolume v R n = modelLogVolume G.hull := by
  unfold Theorem311Source.OriginalInput.sourceHullVolume
  unfold Theorem311Source.OriginalInput.sourceSetVolume
  unfold modelLogVolume
  rw [← hhull]
  apply le_antisymm
  · refine iSup_le fun y => iSup_le fun hy => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hpoint x]
    exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  · refine iSup_le fun x => iSup_le fun hx => ?_
    rw [← hpoint x]
    exact le_iSup_of_le (e x) (le_iSup_of_le ⟨x, hx, rfl⟩ le_rfl)

/-- Conditional finiteness of the actual source hull volume, obtained by
transporting the P3 model's finite log-volume along an explicit carrier
identification.  This is the N7-facing corollary of the model; the remaining
gap is precisely the identification hypothesis. -/
theorem sourceHullVolume_lt_top_of_model_equiv {X : Type uX}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : V) (R : I.SourceImageRealization v)
    (n : Theorem311Source.OriginalInput.ThetaPilotCarrier l)
    (G : OneCircUGeometry X) (e : X ≃ I.ThetaPilotPoint v)
    (hpoint : ∀ x : X, I.sourcePointVolume v (e x) = ENNReal.ofReal ‖x‖)
    (hhull : e '' G.hull =
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))) :
    I.sourceHullVolume v R n < ⊤ := by
  rw [sourceHullVolume_eq_modelLogVolume_of_equiv (I := I) (v := v) (R := R)
    (n := n) (G := G) (e := e) hpoint hhull]
  exact G.hull_logVolume_lt_top

end SourceTransport

end

end LeanFormal.IUT
