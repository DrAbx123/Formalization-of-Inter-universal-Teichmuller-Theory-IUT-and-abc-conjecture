/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project, hull lane (A490)
-/
import tmp.sheaf.lana.iut.Iut.Wall.IdentifiedCopies

/-!
# The hull side of NumericalWall (A490)

Lemma chain for the IsAdelic / InHullOfImage side of NumericalWall
(Iut/Wall/Checks.lean), assembled from the identified-copies model
(Iut/Wall/IdentifiedCopies.lean) and the log-volume computations of
(Iut/Wall/Rss.lean):

* the theta-pilot (Ind1)-image thetaImage D l is adelic (thetaImage_isAdmissible);
* it lies in its own image class, hence in the hull of the image
  (InImage.inHullOfImage);
* its hull hullOf D (thetaImage D l) is adelic (isAdmissible_hullOf) and lies
  in the hull of the image;
* archimedean rescaling by 0 < t <= 1 keeps a region in the hull of the image
  (the lambda * O hull form of IUT III, Remark 3.9.5: t * (a * O_I) <= a * O_I)
  and adds log t to the log-volume (logVol_archScale);
* consequently every x <= -|log(Theta)| is the log-volume of an adelic region
  in the hull of a single (Ind1)-image, and NumericalWall reduces to a single
  log-volume equation on such a region.

No sorry/axiom; all proofs are assembled from the existing LANA port.
-/

namespace Iut

open NumberField MeasureTheory
open scoped Pointwise

universe u

namespace Wall

variable (D : InitialThetaData.{0})

/-- The (Ind1)-image of the theta-pilot region is adelic. -/
theorem hullActual_thetaImage_isAdelic (l : forall i : Fin (nC D), InitialThetaData.Lab (nC D) i) :
    IsAdelic D (thetaImage D l) :=
  fun i => thetaImage_isAdmissible D l i

/-- The (Ind1)-image lies in its own image class. -/
theorem hullActual_thetaImage_inImage (l : forall i : Fin (nC D), InitialThetaData.Lab (nC D) i) :
    InImage D (thetaImage D l) :=
  ⟨l, fun _ => le_rfl⟩

/-- The (Ind1)-image lies in the hull of the image (InImage.inHullOfImage). -/
theorem hullActual_thetaImage_inHullOfImage
    (l : forall i : Fin (nC D), InitialThetaData.Lab (nC D) i) :
    InHullOfImage D (thetaImage D l) :=
  InImage.inHullOfImage D (hullActual_thetaImage_inImage D l)

/-- The hull of the (Ind1)-image is adelic. -/
theorem hullActual_hullOf_thetaImage_isAdelic
    (l : forall i : Fin (nC D), InitialThetaData.Lab (nC D) i) :
    IsAdelic D (hullOf D (thetaImage D l)) :=
  isAdmissible_hullOf D _ (hullActual_thetaImage_isAdelic D l)

/-- The hull of the (Ind1)-image lies in the hull of the image. -/
theorem hullActual_hullOf_thetaImage_inHullOfImage
    (l : forall i : Fin (nC D), InitialThetaData.Lab (nC D) i) :
    InHullOfImage D (hullOf D (thetaImage D l)) :=
  ⟨l, fun _ => le_rfl⟩

/-- Monotonicity of the archimedean rescaling. -/
theorem hullActual_archScale_le_archScale {t : Real} {U V : Region D}
    (hUV : forall i, U i <= V i) : forall i, archScale D t U i <= archScale D t V i := by
  intro i vQ
  rcases vQ with p | _
  · exact hUV i (.finite p)
  · intro y hy c
    change y c ∈ t • LocalTheory.proj D.placeSect .infinite c (V i).region .infinite
    exact Set.smul_set_mono (Set.image_mono (hUV i .infinite)) (hy c)

/-- Archimedean rescaling by 0 < t <= 1 keeps the hull of the (Ind1)-image inside
the hull: t * (a * O_I) <= a * O_I for t <= 1 (Remark 3.9.5, (i)). -/
theorem hullActual_archScale_hullOf_thetaImage_le {t : Real} (ht : 0 < t) (ht1 : t <= 1)
    (l : forall i : Fin (nC D), InitialThetaData.Lab (nC D) i) :
    forall i, archScale D t (hullOf D (thetaImage D l)) i <= hullOf D (thetaImage D l) i := by
  intro i vQ
  rcases vQ with p | _
  · exact subset_rfl
  · intro y hy
    obtain ⟨a, -, hH⟩ := LocalTheory.isHullRegion_of_mem_hullRegions D.placeSect _ .infinite _
      (((LocalTheory.hull D.placeSect (nC D)).system i .infinite).hull_mem_hullRegions
        (thetaImage_isAdmissible D l i (RationalPlace.infinite)))
    have hHi : (hullOf D (thetaImage D l) i).region .infinite =
        (LocalTheory.packet D.placeSect _ .infinite).productRegion fun c =>
          LocalTheory.scaled D.placeSect .infinite c (a c) := hH
    have hy' : forall c, y c ∈ t • LocalTheory.proj D.placeSect .infinite c
        ((hullOf D (thetaImage D l) i).region .infinite) := hy
    rw [hHi]
    intro c
    have hy'' := hy' c
    rw [hHi, LocalTheory.proj_productRegion D.placeSect _
      (fun c => LocalTheory.scaled D.placeSect .infinite c (a c)) (fun c => ⟨_,
        Set.smul_mem_smul_set (LocalTheory.one_mem_integral D.Kt _
          (LocalTheory.tuple D.placeSect _ c))⟩) c] at hy''
    exact LocalConstruct.smul_smul_integralAt_infinite_subset _ ht ht1 hy''

/-- Archimedean rescaling by 0 < t <= 1 preserves lying in the hull of the image. -/
theorem hullActual_inHullOfImage_archScale_of_le_one {t : Real} (ht : 0 < t) (ht1 : t <= 1)
    {U : Region D} (hU : InHullOfImage D U) :
    InHullOfImage D (archScale D t U) := by
  obtain ⟨l, hl⟩ := hU
  refine ⟨l, fun i => ?_⟩
  exact (hullActual_archScale_le_archScale D hl i).trans
    (hullActual_archScale_hullOf_thetaImage_le D ht ht1 l i)

/-- The IsAdelic / InHullOfImage package for the hull of a (Ind1)-image. -/
theorem hullActual_hullOf_thetaImage_package
    (l : forall i : Fin (nC D), InitialThetaData.Lab (nC D) i) :
    IsAdelic D (hullOf D (thetaImage D l)) ∧
      InHullOfImage D (hullOf D (thetaImage D l)) :=
  ⟨hullActual_hullOf_thetaImage_isAdelic D l,
    hullActual_hullOf_thetaImage_inHullOfImage D l⟩

/-- The IsAdelic / InHullOfImage package for LGP * S on an (Ind3)-choice
(inHullOfImage_lgp; the LGP output of the identified-copies model). -/
theorem hullActual_lgp_package (S : Ind3 D) :
    IsAdelic D (lgp D S.1) ∧ InHullOfImage D (lgp D S.1) :=
  ⟨isAdelic_lgp D S.2.1, inHullOfImage_lgp D S⟩

/-- NumericalWall as one log-volume equation: an adelic region in the hull of a
single (Ind1)-image whose log-volume is the q-pilot value -|log(q)|. -/
theorem hullActual_numericalWall_iff_exists_logVol :
    NumericalWall D ↔ ∃ U : Region D, IsAdelic D U ∧ InHullOfImage D U ∧
      logVol D U = (concreteVariantData D).qPilot.lhs := by
  unfold NumericalWall etaQ
  simp only [ValBPS.eta_eq_eta_iff]

/-- Every x <= -|log(Theta)| is realized by an adelic region in the hull of a
single (Ind1)-image, by archimedean rescaling of the hull of the image. -/
theorem hullActual_exists_adelic_inHullOfImage_logVol (x : Real)
    (hx : x <= (concreteVariantData D).rhsData.rhs) :
    ∃ U : Region D, IsAdelic D U ∧ InHullOfImage D U ∧ logVol D U = x := by
  let l : forall i : Fin (nC D), InitialThetaData.Lab (nC D) i :=
    fun i => InitialThetaData.distinguished i
  let H : Region D := hullOf D (thetaImage D l)
  have hH : IsAdelic D H := hullActual_hullOf_thetaImage_isAdelic D l
  have hrhs : logVol D H = (concreteVariantData D).rhsData.rhs :=
    (rhs_eq_logVol_image D l).symm
  let t : Real := Real.exp (x - (concreteVariantData D).rhsData.rhs)
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t <= 1 := Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨archScale D t H, isAdelic_archScale D ht hH, ?_, ?_⟩
  · exact hullActual_inHullOfImage_archScale_of_le_one D ht ht1
      (hullActual_hullOf_thetaImage_inHullOfImage D l)
  · rw [logVol_archScale D ht hH, hrhs, Real.log_exp]
    ring

end Wall

end Iut
