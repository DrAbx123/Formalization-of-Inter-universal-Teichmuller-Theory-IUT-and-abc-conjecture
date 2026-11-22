import tmp.sheaf.xif.paper.Mzk1HullFermatGluingActual
import tmp.sheaf.xif.paper.Mzk1SchemeOpensRangeInterfaceActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1HullFermatGluingActual

/-- The chart ring Q[lambda] (both charts use this ring, with the two coordinate names
lambda and t). -/
abbrev ChartRing : Type := Polynomial ℚ

/-- The overlap ring Q[lambda, lambda^{-1}]. -/
abbrev OverlapRing : Type := Localization.Away (Polynomial.X : Polynomial ℚ)

/-- The class of lambda in the overlap (the structure map of the localization). -/
noncomputable def ovLambda : OverlapRing :=
  algebraMap (Polynomial ℚ) OverlapRing (Polynomial.X : Polynomial ℚ)

/-- The inverse of lambda in the overlap. -/
noncomputable def invLambda : OverlapRing :=
  IsLocalization.Away.invSelf (S := OverlapRing) (x := (Polynomial.X : Polynomial ℚ))

theorem ovLambda_mul_invLambda : ovLambda * invLambda = 1 :=
  IsLocalization.Away.mul_invSelf (S := OverlapRing) (x := (Polynomial.X : Polynomial ℚ))

theorem invLambda_mul_ovLambda : invLambda * ovLambda = 1 := by
  rw [mul_comm]; exact ovLambda_mul_invLambda

theorem invLambda_isUnit : IsUnit invLambda :=
  isUnit_iff_exists_inv.mpr ⟨ovLambda, invLambda_mul_ovLambda⟩

/-- The ring map Q[X] -> overlap sending X to lambda^{-1}. -/
noncomputable def infMapR : Polynomial ℚ →+* OverlapRing :=
  (Polynomial.aeval (R := ℚ) invLambda : Polynomial ℚ →+* OverlapRing)

theorem infMapR_X : infMapR (Polynomial.X) = invLambda := by
  simp [infMapR]

theorem infMapR_C (a : ℚ) : infMapR (Polynomial.C a) = algebraMap ℚ OverlapRing a := by
  simp [infMapR]

/-- The induced ring hom of the overlap: lambda |-> lambda^{-1}. -/
noncomputable def invAuto : OverlapRing →+* OverlapRing :=
  IsLocalization.Away.lift (S := OverlapRing) (x := (Polynomial.X : Polynomial ℚ))
    (g := infMapR) (by rw [infMapR_X]; exact invLambda_isUnit)

theorem invAuto_ovLambda : invAuto ovLambda = invLambda := by
  rw [invAuto, ovLambda, IsLocalization.Away.lift_eq]
  exact infMapR_X

theorem invAuto_invLambda : invAuto invLambda = ovLambda := by
  have h1 : invAuto invLambda * invAuto ovLambda = 1 := by
    rw [← map_mul, invLambda_mul_ovLambda, map_one]
  rw [invAuto_ovLambda] at h1
  calc invAuto invLambda = invAuto invLambda * (invLambda * ovLambda) := by
        rw [invLambda_mul_ovLambda, mul_one]
    _ = (invAuto invLambda * invLambda) * ovLambda := by ring
    _ = ovLambda := by rw [h1, one_mul]

/-- The composite of the inversion with the substitution X |-> lambda^{-1} is the
structure map. -/
theorem invAuto_comp_infMapR : invAuto.comp infMapR = algebraMap (Polynomial ℚ) OverlapRing := by
  apply Polynomial.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, infMapR_C a]
    rw [show algebraMap ℚ OverlapRing a =
        algebraMap (Polynomial ℚ) OverlapRing (Polynomial.C a) from ?_]
    · rw [invAuto, IsLocalization.Away.lift_eq]
      exact infMapR_C a
    · rw [Polynomial.C_eq_algebraMap, IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) OverlapRing a]
  · rw [RingHom.comp_apply, infMapR_X, invAuto_invLambda, ovLambda]

/-- The inversion is an involution. -/
theorem invAuto_comp_self : invAuto.comp invAuto = RingHom.id OverlapRing := by
  have hcomp : (invAuto.comp invAuto).comp (algebraMap (Polynomial ℚ) OverlapRing) =
      algebraMap (Polynomial ℚ) OverlapRing := by
    rw [RingHom.comp_assoc]
    have h1 : invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing) = infMapR :=
      IsLocalization.Away.lift_comp (S := OverlapRing) (x := (Polynomial.X : Polynomial ℚ))
        (g := infMapR) (by rw [infMapR_X]; exact invLambda_isUnit)
    rw [h1, invAuto_comp_infMapR]
  refine IsLocalization.ringHom_ext (M := Submonoid.powers (Polynomial.X : Polynomial ℚ)) ?_
  simpa using hcomp

/-- The inversion automorphism lambda |-> lambda^{-1} of the overlap ring. -/
noncomputable def invAutoEquiv : OverlapRing ≃+* OverlapRing where
  toFun := invAuto
  invFun := invAuto
  left_inv := fun x => RingHom.congr_fun invAuto_comp_self x
  right_inv := fun x => RingHom.congr_fun invAuto_comp_self x
  map_add' := map_add _
  map_mul' := map_mul _

/-! ## The two charts of P^1 and their gluing -/

/-- The first chart Spec Q[lambda]. -/
abbrev chart0Scheme : Scheme := Spec (CommRingCat.of (Polynomial ℚ))
/-- The second chart Spec Q[t]. -/
abbrev chartInfScheme : Scheme := Spec (CommRingCat.of (Polynomial ℚ))
/-- The overlap Spec Q[lambda,lambda^{-1}]. -/
abbrev overlapScheme : Scheme := Spec (CommRingCat.of OverlapRing)

/-- The inclusion of the overlap into the first chart: lambda |-> lambda. -/
noncomputable def overlapToChart0 : overlapScheme ⟶ chart0Scheme :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) OverlapRing))

/-- The inclusion of the overlap into the second chart: t |-> lambda^{-1}. -/
noncomputable def overlapToChartInf : overlapScheme ⟶ chartInfScheme :=
  Spec.map (CommRingCat.ofHom (invAuto.comp (algebraMap (Polynomial ℚ) OverlapRing)))

instance overlapToChart0_isOpenImmersion : IsOpenImmersion overlapToChart0 := by
  rw [overlapToChart0]
  infer_instance

/-- The inversion automorphism is an isomorphism of commutative rings. -/
noncomputable instance invAuto_ofHom_isIso : IsIso (CommRingCat.ofHom invAuto) :=
  invAutoEquiv.toCommRingCatIso.isIso_hom

instance overlapToChartInf_isOpenImmersion : IsOpenImmersion overlapToChartInf := by
  have h : overlapToChartInf =
      Spec.map (CommRingCat.ofHom invAuto) ≫ overlapToChart0 := by
    rw [overlapToChartInf, overlapToChart0, CommRingCat.ofHom_comp, Spec.map_comp]
  rw [h]
  exact IsOpenImmersion.comp _ _

/-- The two-chart gluing data of the projective line. -/
noncomputable def p1GlueData : Scheme.GlueData :=
  twoChartGlueData chart0Scheme chartInfScheme overlapScheme overlapToChart0 overlapToChartInf
    overlapToChart0_isOpenImmersion overlapToChartInf_isOpenImmersion

/-- The canonical projective line: glued from its two standard affine charts along
lambda t = 1. -/
noncomputable abbrev projectiveLineGlued : Scheme := p1GlueData.glued

/-- The lambda-chart of the projective line. -/
noncomputable def localChart0 : chart0Scheme ⟶ projectiveLineGlued :=
  p1GlueData.ι (ULift.up false)

/-- The t-chart of the projective line. -/
noncomputable def localChartInf : chartInfScheme ⟶ projectiveLineGlued :=
  p1GlueData.ι (ULift.up true)

instance localChart0_isOpenImmersion : IsOpenImmersion localChart0 :=
  p1GlueData.ι_isOpenImmersion (ULift.up false)

instance localChartInf_isOpenImmersion : IsOpenImmersion localChartInf :=
  p1GlueData.ι_isOpenImmersion (ULift.up true)

/-- THE OVERLAP COMPATIBILITY (P^1 transition t = lambda^{-1}). -/
theorem localChart_overlap_condition :
    overlapToChartInf ≫ localChartInf = overlapToChart0 ≫ localChart0 :=
  p1GlueData.glue_condition (ULift.up false) (ULift.up true)

/-- The two charts cover P^1. -/
theorem localChart_jointly_surjective (x : projectiveLineGlued) :
    x ∈ Set.range localChart0.base ∪ Set.range localChartInf.base := by
  obtain ⟨i, hi⟩ := p1GlueData.ι_jointly_surjective x
  cases i with
  | up i =>
      cases i
      · exact Or.inl hi
      · exact Or.inr hi

/-- The open range of the overlap inclusion into the t-chart equals the open range of the
composite (invAuto-chart0 inclusion): the two morphisms are equal and the open range does
not depend on the open-immersion instance.  Bridge needed to identify the preimage of the
lambda chart under pi (G-A). -/
theorem overlapToChartInf_opensRange_eq_composite :
    overlapToChartInf.opensRange =
      Scheme.Hom.opensRange (Spec.map (CommRingCat.ofHom invAuto) ≫ overlapToChart0) := by
  have h : overlapToChartInf = Spec.map (CommRingCat.ofHom invAuto) ≫ overlapToChart0 := by
    unfold overlapToChartInf overlapToChart0
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  apply TopologicalSpace.Opens.ext
  rw [LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual.opensRange_coe_eq_range,
    LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual.opensRange_coe_eq_range, h]

#print axioms overlapToChartInf_opensRange_eq_composite
#print axioms invAuto_comp_self
#print axioms invAuto_comp_infMapR
#print axioms overlapToChartInf_isOpenImmersion
#print axioms localChart_overlap_condition
#print axioms localChart_jointly_surjective
end LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
