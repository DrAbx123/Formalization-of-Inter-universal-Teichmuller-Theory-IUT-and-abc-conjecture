/- G-A: the projective line P^1 = Proj Q[X0,X1] is proper.
Route (A): Mathlib's Proj properness theorem (ProjectiveSpectrum/Proper.lean:368)
gives IsProper (Proj.toSpecZero Gr) for Gr finitely generated in degree one;
for Gr = homogeneousSubmodule (Fin 2) Q this is an instance. The degree-zero part
is the base field Q, so the structural morphism over Spec Q is proper too. -/
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartsActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineGluedActual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Tactic
noncomputable section
open AlgebraicGeometry MvPolynomial CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1P1ProperActual

/-- The homogeneous coordinate ring of P^1. -/
abbrev A2 : Type := MvPolynomial (Fin 2) ℚ
/-- Its standard grading. -/
abbrev Gr : ℕ → Submodule ℚ A2 := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ

/-- The standard grading of the homogeneous coordinate ring. -/
instance p1_gradedAlgebra : GradedAlgebra Gr :=
  MvPolynomial.gradedAlgebra

/-- The degree-zero part is a Q-algebra compatibly with the coordinate ring. -/
instance p1_scalarTower : IsScalarTower ℚ (Gr 0) A2 := by
  refine IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := Gr 0) (A := A2) ?_
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply, SetLike.GradeZero.algebraMap_apply,
    SetLike.GradeZero.coe_algebraMap]

/-- The homogeneous coordinate ring is finitely generated over the degree-zero part. -/
instance p1_finiteType : Algebra.FiniteType (Gr 0) A2 := by
  haveI := p1_scalarTower
  exact Algebra.FiniteType.of_restrictScalars_finiteType (R := ℚ) (S := Gr 0) (A := A2)

/-- The structural morphism P^1 = Proj Gr -> Spec (Gr 0). -/
noncomputable def p1ProjToZero :
    (Mzk1G1ProjectiveLineChartsActual.projectiveLine) ⟶
      Spec (CommRingCat.of (Gr 0)) :=
  Proj.toSpecZero Gr

/-- **P^1 is proper over the spectrum of the degree-zero part** (Mathlib's Proj theorem). -/
theorem p1ProjToZero_isProper : IsProper (Proj.toSpecZero Gr) := inferInstance

/-- The constant-coefficient map out of the degree-zero part. -/
def zeroCoeff : (Gr 0) →+* ℚ :=
  letI := MvPolynomial.gradedAlgebra (σ := Fin 2) (R := ℚ)
  (MvPolynomial.constantCoeff : A2 →+* ℚ).comp (algebraMap (Gr 0) A2)

theorem zeroCoeff_algebraMap (c : ℚ) : zeroCoeff (algebraMap ℚ (Gr 0) c) = c := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin 2) (R := ℚ)
  rw [zeroCoeff, RingHom.comp_apply, SetLike.GradeZero.algebraMap_apply,
    SetLike.GradeZero.coe_algebraMap]
  simp [MvPolynomial.algebraMap_eq]

theorem zeroMap_surjective : Function.Surjective (algebraMap ℚ (Gr 0)) := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin 2) (R := ℚ)
  intro y
  have hy : (y : A2) ∈ (1 : Submodule ℚ A2) := by
    rw [← MvPolynomial.homogeneousSubmodule_zero (σ := Fin 2) (R := ℚ)]
    exact y.2
  obtain ⟨c, hc⟩ := Submodule.mem_one.mp hy
  refine ⟨c, Subtype.ext ?_⟩
  rw [SetLike.GradeZero.coe_algebraMap]
  simpa [MvPolynomial.algebraMap_eq] using hc

theorem zeroMap_injective : Function.Injective (algebraMap ℚ (Gr 0)) := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin 2) (R := ℚ)
  intro a b h
  have h' := congrArg zeroCoeff h
  simpa [zeroCoeff_algebraMap] using h'

theorem zeroMap_bijective : Function.Bijective (algebraMap ℚ (Gr 0)) :=
  ⟨zeroMap_injective, zeroMap_surjective⟩

theorem zeroMap_specMap_isIso :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap ℚ (Gr 0)))) := by
  haveI : IsIso (CommRingCat.ofHom (algebraMap ℚ (Gr 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr zeroMap_bijective
  infer_instance

/-- The structural morphism P^1 = Proj Q[X0,X1] -> Spec Q. -/
noncomputable def p1ProjToBase :
    (Mzk1G1ProjectiveLineChartsActual.projectiveLine) ⟶ Spec (CommRingCat.of ℚ) :=
  Proj.toSpecZero Gr ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (Gr 0)))

/-- **P^1 = Proj Q[X0,X1] is proper over Spec Q.** -/
theorem p1ProjToBase_isProper : IsProper p1ProjToBase := by
  haveI := zeroMap_specMap_isIso
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)
    (Proj.toSpecZero Gr) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (Gr 0))))).mpr
    p1ProjToZero_isProper

#print axioms p1ProjToZero_isProper
#print axioms p1ProjToBase_isProper

/-! ## Part 2: the actual G-A target, P^1_glued -> Spec Q -/

section Glued
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual

/-- There is at most one morphism from any scheme to Spec Q, because ring homomorphisms
out of Q are unique. -/
instance subsingleton_hom_spec_rat (X : Scheme) :
    Subsingleton (X ⟶ Spec (CommRingCat.of ℚ)) := by
  constructor
  intro f g
  apply AlgebraicGeometry.ext_to_Spec
  apply CommRingCat.hom_ext
  exact RingHom.ext_rat _ _

/-- The structural morphism of the affine lambda-chart Spec Q[lambda] -> Spec Q. -/
noncomputable def chartBase : chart0Scheme ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (Polynomial ℚ)))

/-- **The structural morphism P^1_glued -> Spec Q**, gluing the two chart structure maps. -/
noncomputable def p1GluedToBase : projectiveLineGlued ⟶ Spec (CommRingCat.of ℚ) :=
  p1GlueData.openCover.glueMorphisms
    (fun i =>
      match i with
      | ULift.up false => chartBase
      | ULift.up true => chartBase)
    (fun i j => Subsingleton.elim _ _)

/-- On the lambda-chart, the glued structure morphism is the chart structure map. -/
theorem localChart0_p1GluedToBase :
    localChart0 ≫ p1GluedToBase = chartBase :=
  p1GlueData.openCover.ι_glueMorphisms _ _ (ULift.up false)

/-- On the t-chart, the glued structure morphism is the chart structure map. -/
theorem localChartInf_p1GluedToBase :
    localChartInf ≫ p1GluedToBase = chartBase :=
  p1GlueData.openCover.ι_glueMorphisms _ _ (ULift.up true)

#print axioms subsingleton_hom_spec_rat
#print axioms p1GluedToBase
end Glued

open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual

/-! ## Part 3: finiteness / compactness properties of the glued structure morphism -/

/-- The affine chart structure maps are of finite type. -/
theorem chartBase_locallyOfFiniteType : LocallyOfFiniteType chartBase := by
  rw [chartBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The affine chart structure maps are quasi-compact. -/
instance chartBase_quasiCompact : QuasiCompact chartBase := inferInstance

/-- The affine chart structure maps are quasi-separated. -/
instance chartBase_quasiSeparated : QuasiSeparated chartBase :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated) (f := chartBase)).mpr inferInstance

/-- Locally of finite type is local at the source, so it suffices to check on the two charts. -/
instance p1GluedToBase_locallyOfFiniteType : LocallyOfFiniteType p1GluedToBase := by
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    p1GlueData.openCover (fun i => ?_)
  cases i with
  | up b =>
    cases b
    · change LocallyOfFiniteType (localChart0 ≫ p1GluedToBase)
      rw [localChart0_p1GluedToBase]
      exact chartBase_locallyOfFiniteType
    · change LocallyOfFiniteType (localChartInf ≫ p1GluedToBase)
      rw [localChartInf_p1GluedToBase]
      exact chartBase_locallyOfFiniteType

/-- The glued projective line is quasi-compact: it is the union of its two compact affine charts. -/
instance projectiveLineGlued_compactSpace : CompactSpace projectiveLineGlued := by
  constructor
  have hcover : (Set.univ : Set projectiveLineGlued) =
      Set.range localChart0.base ∪ Set.range localChartInf.base := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_range, true_iff]
    exact localChart_jointly_surjective x
  rw [hcover]
  exact (isCompact_range localChart0.continuous).union (isCompact_range localChartInf.continuous)

/-- The glued structure morphism is quasi-compact (its affine target and compact source). -/
instance p1GluedToBase_quasiCompact : QuasiCompact p1GluedToBase :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact) (f := p1GluedToBase)).mpr inferInstance

#print axioms chartBase_locallyOfFiniteType
#print axioms p1GluedToBase_locallyOfFiniteType
#print axioms p1GluedToBase_quasiCompact

/-- The chart ranges intersect in the image of the compact overlap scheme. -/
theorem chart_intersection_isCompact :
    IsCompact (Set.range localChart0.base ∩ Set.range localChartInf.base) := by
  let c : PullbackCone localChart0 localChartInf :=
    p1GlueData.vPullbackCone (ULift.up false) (ULift.up true)
  have hpb : IsPullback c.fst c.snd localChart0 localChartInf :=
    IsPullback.of_isLimit (p1GlueData.vPullbackConeIsLimit (ULift.up false) (ULift.up true))
  have hc : IsCompact (Set.range (c.fst ≫ localChart0).base) := by
    change IsCompact (Set.range (overlapToChart0 ≫ localChart0).base)
    exact isCompact_range (overlapToChart0 ≫ localChart0).continuous
  have hrange : Set.range (c.fst ≫ localChart0).base =
      Set.range localChart0.base ∩ Set.range localChartInf.base := by
    have hfac : c.fst ≫ localChart0 =
        hpb.isoPullback.hom ≫ (pullback.fst localChart0 localChartInf ≫ localChart0) := by
      rw [← Category.assoc, hpb.isoPullback_hom_fst]
    rw [hfac, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr (show Function.Surjective ⇑hpb.isoPullback.hom from
        hpb.isoPullback.hom.homeomorph.surjective), Set.image_univ,
      IsOpenImmersion.range_pullback_to_base_of_left]
  rw [← hrange]
  exact hc

/-- The glued projective line is quasi-separated: two affine charts with compact intersection. -/
instance projectiveLineGlued_quasiSeparatedSpace : QuasiSeparatedSpace projectiveLineGlued := by
  let U : Bool → projectiveLineGlued.Opens :=
    fun b => if b then localChartInf.opensRange else localChart0.opensRange
  refine Scheme.quasiSeparatedSpace_of_isOpenCover U ?_ ?_ ?_
  · rw [TopologicalSpace.IsOpenCover]
    ext x
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top, Set.mem_iUnion,
      Set.mem_univ, iff_true, U, Bool.false_eq_true, if_true, if_false,
      Scheme.Hom.coe_opensRange]
    rcases localChart_jointly_surjective x with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · intro b
    cases b with
    | false => exact isAffineOpen_opensRange localChart0
    | true => exact isAffineOpen_opensRange localChartInf
  · intro i j
    cases i <;> cases j
    · simp only [U, Bool.false_eq_true, if_true, if_false, inf_idem,
        TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_opensRange]
      rw [Set.inter_self]
      exact isCompact_range localChart0.continuous
    · simp only [U, Bool.false_eq_true, if_true, if_false,
        TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_opensRange]
      exact chart_intersection_isCompact
    · simp only [U, Bool.false_eq_true, if_true, if_false,
        TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_opensRange]
      rw [Set.inter_comm]
      exact chart_intersection_isCompact
    · simp only [U, Bool.false_eq_true, if_true, if_false, inf_idem,
        TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_opensRange]
      rw [Set.inter_self]
      exact isCompact_range localChartInf.continuous

/-- The glued structure morphism is quasi-separated. -/
instance p1GluedToBase_quasiSeparated : QuasiSeparated p1GluedToBase :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated) (f := p1GluedToBase)).mpr inferInstance

#print axioms chart_intersection_isCompact
#print axioms projectiveLineGlued_quasiSeparatedSpace
#print axioms p1GluedToBase_quasiSeparated

/-- The overlap map identifies the intersection of the two chart ranges. -/
theorem overlap_range_eq :
    Set.range (overlapToChart0 ≫ localChart0).base =
      Set.range localChart0.base ∩ Set.range localChartInf.base := by
  have hpb : IsPullback overlapToChart0 overlapToChartInf localChart0 localChartInf :=
    IsPullback.of_isLimit (p1GlueData.vPullbackConeIsLimit (ULift.up false) (ULift.up true))
  have hfac : overlapToChart0 ≫ localChart0 =
      hpb.isoPullback.hom ≫ (pullback.fst localChart0 localChartInf ≫ localChart0) := by
    rw [← Category.assoc, hpb.isoPullback_hom_fst]
  rw [hfac, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (show Function.Surjective ⇑hpb.isoPullback.hom from
      hpb.isoPullback.hom.homeomorph.surjective), Set.image_univ,
    IsOpenImmersion.range_pullback_to_base_of_left]

/-- The intersection of the two chart opens is the image of the overlap scheme. -/
theorem chart_ranges_inf :
    localChart0.opensRange ⊓ localChartInf.opensRange =
      (overlapToChart0 ≫ localChart0).opensRange := by
  apply TopologicalSpace.Opens.ext
  simp only [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_opensRange, overlap_range_eq]

#print axioms overlap_range_eq
#print axioms chart_ranges_inf

end LeanFormal.IUT.XiFPaper.Mzk1P1ProperActual
