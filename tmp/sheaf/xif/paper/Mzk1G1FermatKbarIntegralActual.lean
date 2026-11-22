/- (h) 路线 2.4 L144 的出口：Y_n ⊗_{Spec ℚ} Spec k̄ 是整概型。

路线（pullback 覆盖，R1）：
记 Ybar := Y_n ×_{Spec ℚ} Spec k̄，两片 U_b := fst ⁻¹ᵁ chartOpenFamily n b 由
kbarCover_iSup_eq_top 覆盖 Ybar。每片由 preimagePullbackIso 与 chart 的 k̄-base change
同构，再经 arrow-iso（Scheme.Hom.isoOpensRange）把 (opensRange).ι ≫ f 换成
chart0ToSpec n，故每片整（isIntegral_pullback_chart0ToSpec）。

两片交非空：交叠 Spec (Overlap0 n) 的 k̄-base change 经 pullback.lift 映入 Ybar
（overlapToYbar），并落在两片交集内 —— 这一步用 Scheme.GlueData.glue_condition
（mem_opensRange_of_glue_condition：ι i (f i j x) ∈ (ι j).opensRange）。

于是 Ybar 既 reduced（逐点用开子概型与全空间的茎同构）又 preirreducible
（PreirreducibleSpace.of_isOpenCover，需两两交非空），且非空，
故整（isIntegral_iff_irreducibleSpace_and_isReduced）。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatKbarSpecActual
import tmp.sheaf.xif.paper.Mzk1SchemePreimagePullbackIsoActual
import tmp.sheaf.xif.paper.Mzk1SchemeGluedIntegralActual
import Mathlib.AlgebraicGeometry.Properties

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Function TopologicalSpace
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatKbarIntegralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatKbarSpecActual
open LeanFormal.IUT.XiFPaper.Mzk1SchemePreimagePullbackIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveToSpecActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmoothFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1HullFermatGluingActual

/-- Ybar n = Y_n ×_{Spec ℚ} Spec k̄。 -/
abbrev Ybar (n : Nat) : Scheme :=
  pullback (fermatCurveToSpec n) gK

/-- Ybar 的两片覆盖开集：chart 开集在 pullback 第一投影下的原像。 -/
abbrev Uopen (n : Nat) (b : Bool) : (Ybar n).Opens :=
  (pullback.fst (fermatCurveToSpec n) gK) ⁻¹ᵁ chartOpenFamily n b

/-- 交叠的 k̄-base change：Spec (Overlap0 n) ×_{Spec ℚ} Spec k̄。 -/
abbrev overlapKbar (n : Nat) : Scheme :=
  pullback (overlapToChart0 n ≫ fermatChart0ToSpec n) gK

/-! ## 一个箭头同构下 pullback 的左因子替换 -/

/-- 若 e : A ≅ B，则 pullback (e.inv ≫ h) g 与 pullback h g 同构。 -/
noncomputable def pullbackIsoCompInv {A B S Z : Scheme} (e : A ≅ B) (h : A ⟶ S)
    (g : Z ⟶ S) : pullback (e.inv ≫ h) g ≅ pullback h g where
  hom := pullback.lift (pullback.fst _ _ ≫ e.inv) (pullback.snd _ _) (by
    rw [Category.assoc]
    exact pullback.condition)
  inv := pullback.lift (pullback.fst _ _ ≫ e.hom) (pullback.snd _ _) (by
    rw [Category.assoc, ← Category.assoc e.hom e.inv h, e.hom_inv_id, Category.id_comp,
      pullback.condition])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

#print axioms pullbackIsoCompInv

/-! ## 胶合数据普通点的横截事实 -/

/-- 胶合数据中，V (i,j) 的点经 f i j 进入第 i 片后，落在第 j 片的开像中。 -/
theorem mem_opensRange_of_glue_condition (D : Scheme.GlueData)
    (i j : D.J) (x : D.V (i, j)) :
    D.ι i (D.f i j x) ∈ (D.ι j).opensRange := by
  refine Scheme.Hom.mem_opensRange.mpr ⟨(D.t i j ≫ D.f j i) x, ?_⟩
  simpa only [Scheme.Hom.comp_apply, Category.assoc] using
    congrArg (fun g => g x) (D.glue_condition i j)

#print axioms mem_opensRange_of_glue_condition

/-! ## 图表结构态射与开像 -/

/-- chart-0 的开浸入复合结构态射与 fermatChart0ToSpec 通过 arrow-iso 对齐。 -/
theorem chartOpen0_comp_eq (n : Nat) :
    (chartOpenFamily n false).ι ≫ fermatCurveToSpec n
      = (fermatChart0ToCurve n).isoOpensRange.inv ≫ fermatChart0ToSpec n := by
  show ((fermatChart0ToCurve n).opensRange).ι ≫ fermatCurveToSpec n
      = (fermatChart0ToCurve n).isoOpensRange.inv ≫ fermatChart0ToSpec n
  rw [← Scheme.Hom.isoOpensRange_inv_comp (fermatChart0ToCurve n), Category.assoc,
    fermatCurveToSpec_ι0]

#print axioms chartOpen0_comp_eq

/-- chart-∞ 的对应版本。 -/
theorem chartOpenInf_comp_eq (n : Nat) :
    (chartOpenFamily n true).ι ≫ fermatCurveToSpec n
      = (fermatChartInfToCurve n).isoOpensRange.inv ≫ fermatChartInfToSpec n := by
  show ((fermatChartInfToCurve n).opensRange).ι ≫ fermatCurveToSpec n
      = (fermatChartInfToCurve n).isoOpensRange.inv ≫ fermatChartInfToSpec n
  rw [← Scheme.Hom.isoOpensRange_inv_comp (fermatChartInfToCurve n), Category.assoc,
    fermatCurveToSpec_ι1]

#print axioms chartOpenInf_comp_eq

/-- 交叠点经 chart-0 映入 Y_n 后落在 chart-∞ 的开像中（glue_condition）。 -/
theorem overlapPoint_mem_chartInf (n : Nat) (x : fermatOverlapScheme n) :
    fermatChart0ToCurve n (overlapToChart0 n x) ∈ (fermatChartInfToCurve n).opensRange :=
  mem_opensRange_of_glue_condition (fermatTwoChartGlueData n) (fermatIdx0 n) (fermatIdx1 n) x

#print axioms overlapPoint_mem_chartInf

/-- overlapToChart0 n ≫ fermatChart0ToSpec n 就是 Spec 上的 ℚ → Overlap0 n。 -/
theorem overlapToChart0_comp_spec (n : Nat) :
    overlapToChart0 n ≫ fermatChart0ToSpec n
      = Spec.map (CommRingCat.ofHom (algebraMap ℚ (Overlap0 n))) := by
  have hL' : ((algebraMap (Chart0Ring n) (Overlap0 n)).comp (algebraMap ℚ (Chart0Ring n)))
      = algebraMap ℚ (Overlap0 n) := RingHom.ext_rat _ _
  rw [overlapToChart0, fermatChart0ToSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hL']

#print axioms overlapToChart0_comp_spec

/-! ## 交叠的 k̄-base change 与它在 Ybar 中的落点 -/

/-- 交叠的 k̄-base change 由 Spec (Overlap0 n ⊗ K) 给出。 -/
noncomputable def overlapKbarIso (n : Nat) :
    overlapKbar n ≅ Spec (CommRingCat.of (Overlap0 n ⊗[ℚ] K)) :=
  pullback.congrHom (overlapToChart0_comp_spec n) rfl ≪≫ pullbackSpecIso ℚ (Overlap0 n) K

#print axioms overlapKbarIso

/-- 交叠的 k̄-base change 非空。 -/
theorem nonempty_overlapKbar (n : Nat) (hn : 0 < n) : Nonempty (overlapKbar n) := by
  obtain ⟨s⟩ := nonempty_overlapKbarSpec n hn
  exact ⟨(overlapKbarIso n).inv s⟩

#print axioms nonempty_overlapKbar

/-- 交叠的 k̄-base change 映入 Ybar。 -/
noncomputable def overlapToYbar (n : Nat) : overlapKbar n ⟶ Ybar n :=
  pullback.lift
    (pullback.fst (overlapToChart0 n ≫ fermatChart0ToSpec n) gK ≫ fermatOverlapToCurve n)
    (pullback.snd (overlapToChart0 n ≫ fermatChart0ToSpec n) gK)
    (by
      simp only [fermatOverlapToCurve, Category.assoc, fermatCurveToSpec_ι0,
        pullback.condition])

#print axioms overlapToYbar

/-- overlapToYbar 的第一投影落点。 -/
theorem fst_overlapToYbar (n : Nat) (q : overlapKbar n) :
    (pullback.fst (fermatCurveToSpec n) gK) (overlapToYbar n q)
      = fermatChart0ToCurve n (overlapToChart0 n
          (pullback.fst (overlapToChart0 n ≫ fermatChart0ToSpec n) gK q)) := by
  have h1 : overlapToYbar n ≫ pullback.fst (fermatCurveToSpec n) gK
      = pullback.fst (overlapToChart0 n ≫ fermatChart0ToSpec n) gK
          ≫ fermatOverlapToCurve n := by
    rw [overlapToYbar, pullback.lift_fst]
  have h2 := congrArg (fun g : overlapKbar n ⟶ fermatCurveScheme n => g q) h1
  simpa only [fermatOverlapToCurve, Scheme.Hom.comp_apply] using h2

#print axioms fst_overlapToYbar

/-- Ybar 中存在同时落在两片覆盖开集内的点。 -/
theorem kbarPoint_exists (n : Nat) (hn : 0 < n) :
    ∃ p : Ybar n, p ∈ Uopen n false ∧ p ∈ Uopen n true := by
  obtain ⟨q⟩ := nonempty_overlapKbar n hn
  refine ⟨overlapToYbar n q, ?_, ?_⟩
  · show (pullback.fst (fermatCurveToSpec n) gK) (overlapToYbar n q) ∈ chartOpenFamily n false
    rw [chartOpenFamily_false, fst_overlapToYbar]
    exact Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩
  · show (pullback.fst (fermatCurveToSpec n) gK) (overlapToYbar n q) ∈ chartOpenFamily n true
    rw [chartOpenFamily_true, fst_overlapToYbar]
    exact overlapPoint_mem_chartInf n _

#print axioms kbarPoint_exists

/-! ## 每片的整性 -/

/-- 第一片 U_false 与 chart-0 的 k̄-base change 同构。 -/
noncomputable def pieceIso0 (n : Nat) :
    (Uopen n false).toScheme ≅ pullback (fermatChart0ToSpec n) gK :=
  preimagePullbackIso (fermatCurveToSpec n) gK (chartOpenFamily n false) ≪≫
    pullback.congrHom (chartOpen0_comp_eq n) rfl ≪≫
      pullbackIsoCompInv (fermatChart0ToCurve n).isoOpensRange (fermatChart0ToSpec n) gK

#print axioms pieceIso0

/-- 第二片 U_true 与 chart-∞ 的 k̄-base change 同构。 -/
noncomputable def pieceIso1 (n : Nat) :
    (Uopen n true).toScheme ≅ pullback (fermatChartInfToSpec n) gK :=
  preimagePullbackIso (fermatCurveToSpec n) gK (chartOpenFamily n true) ≪≫
    pullback.congrHom (chartOpenInf_comp_eq n) rfl ≪≫
      pullbackIsoCompInv (fermatChartInfToCurve n).isoOpensRange (fermatChartInfToSpec n) gK

#print axioms pieceIso1

/-- Ybar 的每片（chart 开集的原像）都是整概型。 -/
theorem isIntegral_piece (n : Nat) (hn : 0 < n) :
    ∀ b : Bool, IsIntegral ((Uopen n b).toScheme) := by
  haveI h0 : IsIntegral (pullback (fermatChart0ToSpec n) gK) :=
    isIntegral_pullback_chart0ToSpec n hn
  haveI h1 : IsIntegral (pullback (fermatChartInfToSpec n) gK) :=
    isIntegral_pullback_chartInfToSpec n hn
  intro b
  cases b
  · exact IsIntegral.of_isIso (pieceIso0 n).inv
  · exact IsIntegral.of_isIso (pieceIso1 n).inv

#print axioms isIntegral_piece

/-! ## 最终定理 -/

/-- route 2.4 L144: Y_n ⊗ k̄ 是整概型。 -/
theorem kbar_integral (n : Nat) (hn : 0 < n) :
    IsIntegral (pullback (fermatCurveToSpec n) gK) := by
  have hU : IsOpenCover (Uopen n) := kbarCover_iSup_eq_top n
  have hpieces : ∀ b : Bool, IsIntegral ((Uopen n b).toScheme) := isIntegral_piece n hn
  obtain ⟨p, hp0, hp1⟩ := kbarPoint_exists n hn
  have hnt : ¬ Disjoint (Uopen n false) (Uopen n true) := by
    rw [← Opens.coe_disjoint]
    exact Set.not_disjoint_iff_nonempty_inter.mpr ⟨p, hp0, hp1⟩
  have htn : ¬ Disjoint (Uopen n true) (Uopen n false) := fun h => hnt (disjoint_comm.mp h)
  haveI hstalk : ∀ x : Ybar n, IsReduced ((Ybar n).presheaf.stalk x) := by
    intro x
    have hx : x ∈ (⨆ b : Bool, Uopen n b) := by
      rw [hU.iSup_eq_top]
      trivial
    rw [Opens.mem_iSup] at hx
    obtain ⟨b, hxb⟩ := hx
    haveI := hpieces b
    exact isReduced_of_injective _
      (Scheme.Opens.stalkIso (Uopen n b) ⟨x, hxb⟩).symm.commRingCatIsoToRingEquiv.injective
  haveI hred : IsReduced (Ybar n) := isReduced_of_isReduced_stalk (Ybar n)
  have hpair : Pairwise ((¬ Disjoint · ·) on Uopen n) := by
    intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · exact hnt
    · exact htn
    · exact absurd rfl hij
  have hpre : ∀ b : Bool, PreirreducibleSpace (Uopen n b) := by
    intro b
    refine Subtype.preirreducibleSpace ?_
    haveI := hpieces b
    have himg : IsPreirreducible
        ((Uopen n b).ι '' (Set.univ : Set ↥((Uopen n b).toScheme))) :=
      (PreirreducibleSpace.isPreirreducible_univ (X := ↥((Uopen n b).toScheme))).image
        (Uopen n b).ι (Scheme.Hom.continuous (Uopen n b).ι).continuousOn
    have hU' : ((Uopen n b).ι '' (Set.univ : Set ↥((Uopen n b).toScheme)))
        = (Uopen n b : Set (Ybar n)) := by
      rw [Set.image_univ, Scheme.Opens.range_ι]
    rw [hU'] at himg
    exact himg
  haveI hpreI : PreirreducibleSpace (Ybar n) :=
    PreirreducibleSpace.of_isOpenCover (U := Uopen n) hpair hU hpre
  haveI hne : Nonempty (Ybar n) := ⟨p⟩
  haveI : IrreducibleSpace (Ybar n) :=
    { toPreirreducibleSpace := hpreI
      toNonempty := hne }
  exact (isIntegral_iff_irreducibleSpace_and_isReduced (X := Ybar n)).mpr ⟨inferInstance, hred⟩

#print axioms kbar_integral

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatKbarIntegralActual
