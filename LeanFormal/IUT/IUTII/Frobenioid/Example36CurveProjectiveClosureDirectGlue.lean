import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveProjectiveClosure
import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
set_option maxHeartbeats 1600000
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

noncomputable abbrev curveProjectiveDirectU (K : Type) [Field K] : Bool → Scheme
  | false => curveScheme K
  | true => curveChartYScheme K

noncomputable abbrev curveProjectiveDirectV (K : Type) [Field K] : Bool × Bool → Scheme
  | (false, false) => curveScheme K
  | (false, true) => curveChartZOverlap K
  | (true, false) => curveChartYOverlap K
  | (true, true) => curveChartYScheme K

noncomputable abbrev curveProjectiveDirectF (K : Type) [Field K] :
    (i j : Bool) → curveProjectiveDirectV K (i, j) ⟶ curveProjectiveDirectU K i
  | false, false => 𝟙 (curveScheme K)
  | false, true => curveChartZOverlapMap K
  | true, false => curveChartYOverlapMap K
  | true, true => 𝟙 (curveChartYScheme K)

noncomputable abbrev curveProjectiveDirectT (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) :
    (i j : Bool) → curveProjectiveDirectV K (i, j) ⟶ curveProjectiveDirectV K (j, i)
  | false, false => 𝟙 (curveScheme K)
  | false, true => e.hom
  | true, false => e.inv
  | true, true => 𝟙 (curveChartYScheme K)

noncomputable def curveProjectiveDirectTPrime (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) (i j k : Bool) :
    pullback (curveProjectiveDirectF K i j) (curveProjectiveDirectF K i k) ⟶
      pullback (curveProjectiveDirectF K j k) (curveProjectiveDirectF K j i) := by
  cases i <;> cases j <;> cases k
  · exact 𝟙 _
  · exact (pullbackSymmetry _ _).hom
  · exact pullback.fst _ _ ≫ curveProjectiveDirectT K e false true ≫
      inv (pullback.snd _ _)
  · exact pullback.fst _ _ ≫ curveProjectiveDirectT K e false true ≫
      inv (pullback.snd _ _)
  · exact pullback.fst _ _ ≫ curveProjectiveDirectT K e true false ≫
      inv (pullback.snd _ _)
  · exact pullback.fst _ _ ≫ curveProjectiveDirectT K e true false ≫
      inv (pullback.snd _ _)
  · exact (pullbackSymmetry _ _).hom
  · exact 𝟙 _


noncomputable abbrev curveProjectiveDirectGlueData (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) : Scheme.GlueData where
  toGlueData :=
    { J := Bool
      U := curveProjectiveDirectU K
      V := curveProjectiveDirectV K
      f := curveProjectiveDirectF K
      f_mono i j := by
        cases i <;> cases j <;> dsimp only [curveProjectiveDirectF] <;> infer_instance
      f_hasPullback i j k := by
        cases i <;> cases j <;> cases k <;>
          dsimp only [curveProjectiveDirectF] <;> infer_instance
      f_id i := by
        cases i <;> dsimp only [curveProjectiveDirectF] <;> infer_instance
      t := curveProjectiveDirectT K e
      t_id i := by cases i <;> rfl
      t' := curveProjectiveDirectTPrime K e
      t_fac i j k := by
        cases i <;> cases j <;> cases k <;>
          simp [curveProjectiveDirectTPrime, curveProjectiveDirectT, curveProjectiveDirectF,
            curveProjectiveDirectU, curveProjectiveDirectV, fst_eq_snd_of_mono_eq,
            pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst, Category.assoc]
      cocycle i j k := by
        cases i <;> cases j <;> cases k <;>
          simp [curveProjectiveDirectTPrime, curveProjectiveDirectT, curveProjectiveDirectF,
            curveProjectiveDirectU, curveProjectiveDirectV, fst_eq_snd_of_mono_eq,
            pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst,
            pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_snd, pullbackSymmetry_fst_inv_snd,
            IsIso.inv_hom_id, e.hom_inv_id, e.inv_hom_id,
            Category.assoc, pullback.condition_assoc] }
  f_open i j := by
    dsimp only [curveProjectiveDirectF]
    cases i <;> cases j
    · exact inferInstance
    · exact inferInstance
    · exact inferInstance
    · exact inferInstance

/-! ## The glued scheme of the direct glue data and its off-diagonal maps -/

/-- The glued scheme of the direct two-chart glue data. -/
noncomputable abbrev curveProjectiveDirectGluedScheme (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) : Scheme :=
  (curveProjectiveDirectGlueData K e).glued

/-- The first chart open immersion of the direct glued scheme. -/
noncomputable abbrev curveProjectiveDirectChartZMap (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) :
    curveScheme K ⟶ curveProjectiveDirectGluedScheme K e :=
  (curveProjectiveDirectGlueData K e).ι false

instance curveProjectiveDirectChartZMap_isOpenImmersion (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) :
    IsOpenImmersion (curveProjectiveDirectChartZMap K e) :=
  (curveProjectiveDirectGlueData K e).ι_isOpenImmersion false

/-- The second chart open immersion of the direct glued scheme. -/
noncomputable abbrev curveProjectiveDirectChartYMap (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) :
    curveChartYScheme K ⟶ curveProjectiveDirectGluedScheme K e :=
  (curveProjectiveDirectGlueData K e).ι true

instance curveProjectiveDirectChartYMap_isOpenImmersion (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) :
    IsOpenImmersion (curveProjectiveDirectChartYMap K e) :=
  (curveProjectiveDirectGlueData K e).ι_isOpenImmersion true

/-- The point at infinity on the direct glued scheme (via the chart `Y = 1`). -/
noncomputable abbrev curveProjectiveDirectPointAtInfinity (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) :
    curveProjectiveDirectGluedScheme K e :=
  curveProjectiveDirectChartYMap K e (curveInfinityPoint K)

/-- The two direct charts jointly cover the direct glued scheme. -/
theorem curveProjectiveDirectCharts_jointly_surjective (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K)
    (x : curveProjectiveDirectGluedScheme K e) :
    (∃ y, curveProjectiveDirectChartZMap K e y = x) ∨
      (∃ y, curveProjectiveDirectChartYMap K e y = x) := by
  obtain ⟨i, y, hy⟩ := (curveProjectiveDirectGlueData K e).openCover.exists_eq x
  cases i
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

/-! ## Off-diagonal maps of the direct glue data

These are definitional computations for the `match` definition of the explicit
`Scheme.GlueData`. -/

theorem curveProjectiveDirectGlueData_f_false_true (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) :
    (curveProjectiveDirectGlueData K e).f false true = curveChartZOverlapMap K :=
  rfl

theorem curveProjectiveDirectGlueData_f_true_false (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) :
    (curveProjectiveDirectGlueData K e).f true false = curveChartYOverlapMap K :=
  rfl

theorem curveProjectiveDirectGlueData_t_false_true (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) :
    (curveProjectiveDirectGlueData K e).t false true = e.hom :=
  rfl

theorem curveProjectiveDirectGlueData_t_true_false (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) :
    (curveProjectiveDirectGlueData K e).t true false = e.inv :=
  rfl

/-! ## The direct glued scheme is the projective closure

For the actual transition isomorphism both glue data have the same two charts and
the same overlap identifications; the comparison morphisms are assembled from the
multicoequalizer universal property and proved inverse by chart extensionality. -/

/-- The chart map used to descend the direct glued scheme to the projective closure. -/
noncomputable def curveProjectiveDirectToProjectiveChartMap (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) (b : Bool) :
    (curveProjectiveDirectGlueData K e).U b ⟶ curveProjectiveGluedScheme K :=
  match b with
  | false => curveProjectiveChartZMap K
  | true => curveProjectiveChartYMap K

/-- The cocone compatibility for `curveProjectiveDirectToProjectiveGlued`. -/
theorem curveProjectiveDirectToProjective_desc_compat (K : Type) [Field K] (i j : Bool) :
    (curveProjectiveDirectGlueData K (curveChartOverlapTransitionIso K)).f i j ≫
        curveProjectiveDirectToProjectiveChartMap K (curveChartOverlapTransitionIso K) i =
      ((curveProjectiveDirectGlueData K (curveChartOverlapTransitionIso K)).t i j ≫
          (curveProjectiveDirectGlueData K (curveChartOverlapTransitionIso K)).f j i) ≫
        curveProjectiveDirectToProjectiveChartMap K (curveChartOverlapTransitionIso K) j := by
  cases i <;> cases j
  · simp [curveProjectiveDirectToProjectiveChartMap]
  · rw [curveProjectiveDirectGlueData_f_false_true K (curveChartOverlapTransitionIso K),
      curveProjectiveDirectGlueData_t_false_true K (curveChartOverlapTransitionIso K),
      curveProjectiveDirectGlueData_f_true_false K (curveChartOverlapTransitionIso K), Category.assoc]
    change curveChartZOverlapMap K ≫ curveProjectiveChartZMap K =
      (curveChartOverlapTransitionIso K).hom ≫ curveChartYOverlapMap K ≫
        curveProjectiveChartYMap K
    exact ((curveProjectiveSchemeGlueData K).glue_condition false true).symm
  · rw [curveProjectiveDirectGlueData_f_true_false K (curveChartOverlapTransitionIso K),
      curveProjectiveDirectGlueData_t_true_false K (curveChartOverlapTransitionIso K),
      curveProjectiveDirectGlueData_f_false_true K (curveChartOverlapTransitionIso K), Category.assoc]
    change curveChartYOverlapMap K ≫ curveProjectiveChartYMap K =
      (curveChartOverlapTransitionIso K).inv ≫ curveChartZOverlapMap K ≫
        curveProjectiveChartZMap K
    exact ((curveProjectiveSchemeGlueData K).glue_condition true false).symm
  · simp [curveProjectiveDirectToProjectiveChartMap]

/-- The comparison morphism from the direct glued scheme (with the actual
transition isomorphism) to the projective closure. -/
noncomputable def curveProjectiveDirectToProjectiveGlued (K : Type) [Field K] :
    curveProjectiveDirectGluedScheme K (curveChartOverlapTransitionIso K) ⟶
      curveProjectiveGluedScheme K := by
  classical
  let e := curveChartOverlapTransitionIso K
  haveI : HasMulticoequalizer (curveProjectiveDirectGlueData K e).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram _
  refine Multicoequalizer.desc (curveProjectiveDirectGlueData K e).diagram
    (curveProjectiveGluedScheme K)
    (curveProjectiveDirectToProjectiveChartMap K e) ?_
  rintro ⟨i, j⟩
  exact curveProjectiveDirectToProjective_desc_compat K i j

/-- The chart map used to descend the projective closure to the direct glued scheme. -/
noncomputable def curveProjectiveProjectiveToDirectChartMap (K : Type) [Field K]
    (e : curveChartZOverlap K ≅ curveChartYOverlap K) (b : Bool) :
    (curveProjectiveSchemeGlueData K).U b ⟶ curveProjectiveDirectGluedScheme K e :=
  match b with
  | false => curveProjectiveDirectChartZMap K e
  | true => curveProjectiveDirectChartYMap K e

/-- The cocone compatibility for `curveProjectiveProjectiveToDirectGlued`. -/
theorem curveProjectiveProjectiveToDirect_desc_compat (K : Type) [Field K] (i j : Bool) :
    (curveProjectiveSchemeGlueData K).f i j ≫
        curveProjectiveProjectiveToDirectChartMap K (curveChartOverlapTransitionIso K) i =
      ((curveProjectiveSchemeGlueData K).t i j ≫
          (curveProjectiveSchemeGlueData K).f j i) ≫
        curveProjectiveProjectiveToDirectChartMap K (curveChartOverlapTransitionIso K) j := by
  cases i <;> cases j
  · simp [curveProjectiveProjectiveToDirectChartMap]
  · rw [curveProjectiveSchemeGlueData_f_false_true K,
      curveProjectiveSchemeGlueData_t_false_true K,
      curveProjectiveSchemeGlueData_f_true_false K, Category.assoc]
    change curveChartZOverlapMap K ≫
        curveProjectiveDirectChartZMap K (curveChartOverlapTransitionIso K) =
      (curveChartOverlapTransitionIso K).hom ≫ curveChartYOverlapMap K ≫
        curveProjectiveDirectChartYMap K (curveChartOverlapTransitionIso K)
    exact ((curveProjectiveDirectGlueData K (curveChartOverlapTransitionIso K)).glue_condition false true).symm
  · rw [curveProjectiveSchemeGlueData_f_true_false K,
      curveProjectiveSchemeGlueData_t_true_false K,
      curveProjectiveSchemeGlueData_f_false_true K, Category.assoc]
    change curveChartYOverlapMap K ≫
        curveProjectiveDirectChartYMap K (curveChartOverlapTransitionIso K) =
      (curveChartOverlapTransitionIso K).inv ≫ curveChartZOverlapMap K ≫
        curveProjectiveDirectChartZMap K (curveChartOverlapTransitionIso K)
    exact ((curveProjectiveDirectGlueData K (curveChartOverlapTransitionIso K)).glue_condition true false).symm
  · simp [curveProjectiveProjectiveToDirectChartMap]

/-- The comparison morphism from the projective closure to the direct glued
scheme (with the actual transition isomorphism). -/
noncomputable def curveProjectiveProjectiveToDirectGlued (K : Type) [Field K] :
    curveProjectiveGluedScheme K ⟶
      curveProjectiveDirectGluedScheme K (curveChartOverlapTransitionIso K) := by
  classical
  let e := curveChartOverlapTransitionIso K
  haveI : HasMulticoequalizer (curveProjectiveSchemeGlueData K).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram _
  refine Multicoequalizer.desc (curveProjectiveSchemeGlueData K).diagram
    (curveProjectiveDirectGluedScheme K e)
    (curveProjectiveProjectiveToDirectChartMap K e) ?_
  rintro ⟨i, j⟩
  exact curveProjectiveProjectiveToDirect_desc_compat K i j

/-- The first chart of the direct glued scheme maps to the first chart of the
projective closure. -/
theorem curveProjectiveDirectToProjectiveGlued_chartZ (K : Type) [Field K] :
    curveProjectiveDirectChartZMap K (curveChartOverlapTransitionIso K) ≫
        curveProjectiveDirectToProjectiveGlued K =
      curveProjectiveChartZMap K := by
  classical
  let e := curveChartOverlapTransitionIso K
  haveI : HasMulticoequalizer (curveProjectiveDirectGlueData K e).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram _
  unfold curveProjectiveDirectChartZMap curveProjectiveDirectToProjectiveGlued
  exact Multicoequalizer.π_desc (curveProjectiveDirectGlueData K e).diagram
    (curveProjectiveGluedScheme K)
    (curveProjectiveDirectToProjectiveChartMap K e)
    (fun a => curveProjectiveDirectToProjective_desc_compat K a.1 a.2) false

/-- The second chart of the direct glued scheme maps to the second chart of the
projective closure. -/
theorem curveProjectiveDirectToProjectiveGlued_chartY (K : Type) [Field K] :
    curveProjectiveDirectChartYMap K (curveChartOverlapTransitionIso K) ≫
        curveProjectiveDirectToProjectiveGlued K =
      curveProjectiveChartYMap K := by
  classical
  let e := curveChartOverlapTransitionIso K
  haveI : HasMulticoequalizer (curveProjectiveDirectGlueData K e).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram _
  unfold curveProjectiveDirectChartYMap curveProjectiveDirectToProjectiveGlued
  exact Multicoequalizer.π_desc (curveProjectiveDirectGlueData K e).diagram
    (curveProjectiveGluedScheme K)
    (curveProjectiveDirectToProjectiveChartMap K e)
    (fun a => curveProjectiveDirectToProjective_desc_compat K a.1 a.2) true

/-- The first chart of the projective closure maps to the first chart of the
direct glued scheme. -/
theorem curveProjectiveProjectiveToDirectGlued_chartZ (K : Type) [Field K] :
    curveProjectiveChartZMap K ≫ curveProjectiveProjectiveToDirectGlued K =
      curveProjectiveDirectChartZMap K (curveChartOverlapTransitionIso K) := by
  classical
  let e := curveChartOverlapTransitionIso K
  haveI : HasMulticoequalizer (curveProjectiveSchemeGlueData K).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram _
  unfold curveProjectiveChartZMap curveProjectiveProjectiveToDirectGlued
  exact Multicoequalizer.π_desc (curveProjectiveSchemeGlueData K).diagram
    (curveProjectiveDirectGluedScheme K e)
    (curveProjectiveProjectiveToDirectChartMap K e)
    (fun a => curveProjectiveProjectiveToDirect_desc_compat K a.1 a.2) false

/-- The second chart of the projective closure maps to the second chart of the
direct glued scheme. -/
theorem curveProjectiveProjectiveToDirectGlued_chartY (K : Type) [Field K] :
    curveProjectiveChartYMap K ≫ curveProjectiveProjectiveToDirectGlued K =
      curveProjectiveDirectChartYMap K (curveChartOverlapTransitionIso K) := by
  classical
  let e := curveChartOverlapTransitionIso K
  haveI : HasMulticoequalizer (curveProjectiveSchemeGlueData K).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram _
  unfold curveProjectiveChartYMap curveProjectiveProjectiveToDirectGlued
  exact Multicoequalizer.π_desc (curveProjectiveSchemeGlueData K).diagram
    (curveProjectiveDirectGluedScheme K e)
    (curveProjectiveProjectiveToDirectChartMap K e)
    (fun a => curveProjectiveProjectiveToDirect_desc_compat K a.1 a.2) true

/-- The two comparison morphisms are inverse: the direct glued scheme with the
actual transition isomorphism is isomorphic to the projective closure. -/
noncomputable def curveProjectiveDirectGluedIso (K : Type) [Field K] :
    curveProjectiveDirectGluedScheme K (curveChartOverlapTransitionIso K) ≅
      curveProjectiveGluedScheme K where
  hom := curveProjectiveDirectToProjectiveGlued K
  inv := curveProjectiveProjectiveToDirectGlued K
  hom_inv_id := by
    classical
    let e := curveChartOverlapTransitionIso K
    haveI : HasMulticoequalizer (curveProjectiveDirectGlueData K e).diagram :=
      Scheme.GlueData.instHasMulticoequalizerDiagram _
    apply Multicoequalizer.hom_ext
    intro b
    cases b
    · change curveProjectiveDirectChartZMap K e ≫
        (curveProjectiveDirectToProjectiveGlued K ≫
          curveProjectiveProjectiveToDirectGlued K) =
        curveProjectiveDirectChartZMap K e ≫ 𝟙 _
      calc curveProjectiveDirectChartZMap K e ≫
            (curveProjectiveDirectToProjectiveGlued K ≫
              curveProjectiveProjectiveToDirectGlued K)
          = (curveProjectiveDirectChartZMap K e ≫
              curveProjectiveDirectToProjectiveGlued K) ≫
              curveProjectiveProjectiveToDirectGlued K := by rw [Category.assoc]
        _ = curveProjectiveChartZMap K ≫
              curveProjectiveProjectiveToDirectGlued K := by
            rw [curveProjectiveDirectToProjectiveGlued_chartZ]
        _ = curveProjectiveDirectChartZMap K e := by
            rw [curveProjectiveProjectiveToDirectGlued_chartZ]
        _ = curveProjectiveDirectChartZMap K e ≫ 𝟙 _ := by rw [Category.comp_id]
    · change curveProjectiveDirectChartYMap K e ≫
        (curveProjectiveDirectToProjectiveGlued K ≫
          curveProjectiveProjectiveToDirectGlued K) =
        curveProjectiveDirectChartYMap K e ≫ 𝟙 _
      calc curveProjectiveDirectChartYMap K e ≫
            (curveProjectiveDirectToProjectiveGlued K ≫
              curveProjectiveProjectiveToDirectGlued K)
          = (curveProjectiveDirectChartYMap K e ≫
              curveProjectiveDirectToProjectiveGlued K) ≫
              curveProjectiveProjectiveToDirectGlued K := by rw [Category.assoc]
        _ = curveProjectiveChartYMap K ≫
              curveProjectiveProjectiveToDirectGlued K := by
            rw [curveProjectiveDirectToProjectiveGlued_chartY]
        _ = curveProjectiveDirectChartYMap K e := by
            rw [curveProjectiveProjectiveToDirectGlued_chartY]
        _ = curveProjectiveDirectChartYMap K e ≫ 𝟙 _ := by rw [Category.comp_id]
  inv_hom_id := by
    classical
    haveI : HasMulticoequalizer (curveProjectiveSchemeGlueData K).diagram :=
      Scheme.GlueData.instHasMulticoequalizerDiagram _
    apply Multicoequalizer.hom_ext
    intro b
    cases b
    · change curveProjectiveChartZMap K ≫
        (curveProjectiveProjectiveToDirectGlued K ≫
          curveProjectiveDirectToProjectiveGlued K) =
        curveProjectiveChartZMap K ≫ 𝟙 _
      calc curveProjectiveChartZMap K ≫
            (curveProjectiveProjectiveToDirectGlued K ≫
              curveProjectiveDirectToProjectiveGlued K)
          = (curveProjectiveChartZMap K ≫
              curveProjectiveProjectiveToDirectGlued K) ≫
              curveProjectiveDirectToProjectiveGlued K := by rw [Category.assoc]
        _ = curveProjectiveDirectChartZMap K (curveChartOverlapTransitionIso K) ≫
              curveProjectiveDirectToProjectiveGlued K := by
            rw [curveProjectiveProjectiveToDirectGlued_chartZ]
        _ = curveProjectiveChartZMap K := by
            rw [curveProjectiveDirectToProjectiveGlued_chartZ]
        _ = curveProjectiveChartZMap K ≫ 𝟙 _ := by rw [Category.comp_id]
    · change curveProjectiveChartYMap K ≫
        (curveProjectiveProjectiveToDirectGlued K ≫
          curveProjectiveDirectToProjectiveGlued K) =
        curveProjectiveChartYMap K ≫ 𝟙 _
      calc curveProjectiveChartYMap K ≫
            (curveProjectiveProjectiveToDirectGlued K ≫
              curveProjectiveDirectToProjectiveGlued K)
          = (curveProjectiveChartYMap K ≫
              curveProjectiveProjectiveToDirectGlued K) ≫
              curveProjectiveDirectToProjectiveGlued K := by rw [Category.assoc]
        _ = curveProjectiveDirectChartYMap K (curveChartOverlapTransitionIso K) ≫
              curveProjectiveDirectToProjectiveGlued K := by
            rw [curveProjectiveProjectiveToDirectGlued_chartY]
        _ = curveProjectiveChartYMap K := by
            rw [curveProjectiveDirectToProjectiveGlued_chartY]
        _ = curveProjectiveChartYMap K ≫ 𝟙 _ := by rw [Category.comp_id]


noncomputable abbrev curveProjectiveDirectD (K : Type) [Field K] : Scheme.GlueData :=
  curveProjectiveDirectGlueData K (curveChartOverlapTransitionIso K)

/-- The chart structure maps used to descend the direct glued scheme. -/
noncomputable abbrev curveProjectiveDirectChartStruct (K : Type) [Field K] :
    (i : Bool) → (curveProjectiveDirectD K).U i ⟶ Spec (CommRingCat.of K)
  | false => curveSchemeStructureMap K
  | true => curveChartYStructureMap K

/-- Compatibility of the chart structure maps with the direct glue data. -/
theorem curveProjectiveDirectCharts_compat (K : Type) [Field K] :
    ∀ (i j : Bool),
      pullback.fst ((curveProjectiveDirectD K).ι i) ((curveProjectiveDirectD K).ι j) ≫
          curveProjectiveDirectChartStruct K i =
        pullback.snd ((curveProjectiveDirectD K).ι i) ((curveProjectiveDirectD K).ι j) ≫
          curveProjectiveDirectChartStruct K j := by
  intro i j
  cases i <;> cases j
  · rw [show pullback.fst ((curveProjectiveDirectD K).ι false)
          ((curveProjectiveDirectD K).ι false) =
        pullback.snd ((curveProjectiveDirectD K).ι false)
          ((curveProjectiveDirectD K).ι false) from
      (cancel_mono ((curveProjectiveDirectD K).ι false)).mp
        (by simpa using pullback.condition)]
  · let c : (curveProjectiveDirectD K).V (false, true) ≅
        pullback ((curveProjectiveDirectD K).ι false) ((curveProjectiveDirectD K).ι true) :=
      IsLimit.conePointUniqueUpToIso ((curveProjectiveDirectD K).vPullbackConeIsLimit false true)
        (pullback.isLimit ((curveProjectiveDirectD K).ι false)
          ((curveProjectiveDirectD K).ι true))
    apply (cancel_epi c.hom).mp
    have hfst : c.hom ≫ pullback.fst ((curveProjectiveDirectD K).ι false)
        ((curveProjectiveDirectD K).ι true) =
        ((curveProjectiveDirectD K).vPullbackCone false true).fst :=
      IsLimit.conePointUniqueUpToIso_hom_comp
        ((curveProjectiveDirectD K).vPullbackConeIsLimit false true)
        (pullback.isLimit ((curveProjectiveDirectD K).ι false)
          ((curveProjectiveDirectD K).ι true)) WalkingCospan.left
    have hsnd : c.hom ≫ pullback.snd ((curveProjectiveDirectD K).ι false)
        ((curveProjectiveDirectD K).ι true) =
        ((curveProjectiveDirectD K).vPullbackCone false true).snd :=
      IsLimit.conePointUniqueUpToIso_hom_comp
        ((curveProjectiveDirectD K).vPullbackConeIsLimit false true)
        (pullback.isLimit ((curveProjectiveDirectD K).ι false)
          ((curveProjectiveDirectD K).ι true)) WalkingCospan.right
    rw [← Category.assoc, hfst]
    change (curveProjectiveDirectD K).f false true ≫
        curveProjectiveDirectChartStruct K false =
      c.hom ≫ pullback.snd ((curveProjectiveDirectD K).ι false)
        ((curveProjectiveDirectD K).ι true) ≫ curveProjectiveDirectChartStruct K true
    rw [← Category.assoc, hsnd]
    change (curveProjectiveDirectD K).f false true ≫
        curveProjectiveDirectChartStruct K false =
      ((curveProjectiveDirectD K).t false true ≫
        (curveProjectiveDirectD K).f true false) ≫ curveProjectiveDirectChartStruct K true
    simpa [curveProjectiveDirectD, curveProjectiveDirectGlueData,
      curveProjectiveDirectF, curveProjectiveDirectT, curveProjectiveDirectChartStruct,
      curveChartOverlapTransitionIso_hom] using
      (curveChartOverlapTransitionIso_structure_compat K).symm
  · let c : (curveProjectiveDirectD K).V (true, false) ≅
        pullback ((curveProjectiveDirectD K).ι true) ((curveProjectiveDirectD K).ι false) :=
      IsLimit.conePointUniqueUpToIso ((curveProjectiveDirectD K).vPullbackConeIsLimit true false)
        (pullback.isLimit ((curveProjectiveDirectD K).ι true)
          ((curveProjectiveDirectD K).ι false))
    apply (cancel_epi c.hom).mp
    have hfst : c.hom ≫ pullback.fst ((curveProjectiveDirectD K).ι true)
        ((curveProjectiveDirectD K).ι false) =
        ((curveProjectiveDirectD K).vPullbackCone true false).fst :=
      IsLimit.conePointUniqueUpToIso_hom_comp
        ((curveProjectiveDirectD K).vPullbackConeIsLimit true false)
        (pullback.isLimit ((curveProjectiveDirectD K).ι true)
          ((curveProjectiveDirectD K).ι false)) WalkingCospan.left
    have hsnd : c.hom ≫ pullback.snd ((curveProjectiveDirectD K).ι true)
        ((curveProjectiveDirectD K).ι false) =
        ((curveProjectiveDirectD K).vPullbackCone true false).snd :=
      IsLimit.conePointUniqueUpToIso_hom_comp
        ((curveProjectiveDirectD K).vPullbackConeIsLimit true false)
        (pullback.isLimit ((curveProjectiveDirectD K).ι true)
          ((curveProjectiveDirectD K).ι false)) WalkingCospan.right
    rw [← Category.assoc, hfst]
    change (curveProjectiveDirectD K).f true false ≫
        curveProjectiveDirectChartStruct K true =
      c.hom ≫ pullback.snd ((curveProjectiveDirectD K).ι true)
        ((curveProjectiveDirectD K).ι false) ≫ curveProjectiveDirectChartStruct K false
    rw [← Category.assoc, hsnd]
    change (curveProjectiveDirectD K).f true false ≫
        curveProjectiveDirectChartStruct K true =
      ((curveProjectiveDirectD K).t true false ≫
        (curveProjectiveDirectD K).f false true) ≫ curveProjectiveDirectChartStruct K false
    simpa [curveProjectiveDirectD, curveProjectiveDirectGlueData,
      curveProjectiveDirectF, curveProjectiveDirectT, curveProjectiveDirectChartStruct,
      curveChartOverlapTransitionIso_inv] using
      (curveChartOverlapTransitionIso_structure_compat_inv K).symm
  · rw [show pullback.fst ((curveProjectiveDirectD K).ι true)
          ((curveProjectiveDirectD K).ι true) =
        pullback.snd ((curveProjectiveDirectD K).ι true)
          ((curveProjectiveDirectD K).ι true) from
      (cancel_mono ((curveProjectiveDirectD K).ι true)).mp
        (by simpa using pullback.condition)]

/-- The structure morphism from the direct glued scheme to `Spec K`. -/
noncomputable def curveProjectiveDirectStructureMap (K : Type) [Field K] :
    (curveProjectiveDirectD K).glued ⟶ Spec (CommRingCat.of K) :=
  (curveProjectiveDirectD K).openCover.glueMorphisms (curveProjectiveDirectChartStruct K)
    (curveProjectiveDirectCharts_compat K)

theorem curveProjectiveDirectStructureMap_ι (K : Type) [Field K] (i : Bool) :
    (curveProjectiveDirectD K).ι i ≫ curveProjectiveDirectStructureMap K =
      curveProjectiveDirectChartStruct K i := by
  simpa [curveProjectiveDirectStructureMap, Scheme.GlueData.openCover] using
    Scheme.Cover.ι_glueMorphisms (curveProjectiveDirectD K).openCover
      (curveProjectiveDirectChartStruct K) (curveProjectiveDirectCharts_compat K) i

/-- The direct glued scheme with the actual transition isomorphism inhabits the
projective closure card. -/
noncomputable def curveProjectiveDirectGlueCard (K : Type) [Field K] :
    CurveProjectiveClosureGlueCard K :=
  { transitionIso := curveChartOverlapTransitionIso K
    glueData := curveProjectiveDirectD K
    projectiveScheme := (curveProjectiveDirectD K).glued
    projectiveScheme_eq_glued := rfl
    chartZOpenImmersion := (curveProjectiveDirectD K).ι false
    chartYOpenImmersion := (curveProjectiveDirectD K).ι true
    structureMap := curveProjectiveDirectStructureMap K
    pointAtInfinity := (curveProjectiveDirectD K).ι true (curveInfinityPoint K) }

theorem curveProjectiveDirectGlueCardRealized (K : Type) [Field K] :
    CurveProjectiveClosureGlueCardRealized K :=
  ⟨curveProjectiveDirectGlueCard K⟩

end Example36
end LeanFormal.IUT.IUTII.Frobenioid