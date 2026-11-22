import tmp.sheaf.xif.paper.Mzk1G1PsiAffineCompatActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import tmp.sheaf.xif.paper.Mzk1G1PsiChartInfCoverActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartPreimageActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartInfCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1HullFermatGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual

variable (n : Nat) (T : Finset ℚ)

/-- The D(q) piece of the second chart, mapped into Y_n. -/
noncomputable def qPiece :
    Spec (CommRingCat.of (Localization.Away (psiChartInfDenom n T))) ⟶ fermatCurveScheme n :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)))) ≫
    fermatChartInfToCurve n

instance qPiece_isOpenImmersion : IsOpenImmersion (qPiece n T) := by
  unfold qPiece
  infer_instance

/-- A point of Spec R2 lies in the range of the localization at f iff f is not in it. -/
theorem mem_range_localization_iff (f : R2 n) (z : PrimeSpectrum (R2 n)) :
    z ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (R2 n) (Localization.Away f))) ↔ f ∉ z.asIdeal := by
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
  exact PrimeSpectrum.mem_basicOpen f z

/-- In a prime of the second chart, q and r cannot both vanish: q*r generates the unit ideal. -/
theorem not_mem_chartR_of_mem_denom {z : PrimeSpectrum (R2 n)}
    (hq : psiChartInfDenom n T ∈ z.asIdeal) : chartR n ∉ z.asIdeal := by
  intro hr
  have hle : Ideal.span ({psiChartInfDenom n T, chartR n} : Set (R2 n)) ≤ z.asIdeal := by
    rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hq
    · exact hr
  have h1 : (1 : R2 n) ∈ z.asIdeal := by
    have htop : Ideal.span ({psiChartInfDenom n T, chartR n} : Set (R2 n)) = ⊤ :=
      span_denom_chartR_eq_top n T
    have : (1 : R2 n) ∈ Ideal.span ({psiChartInfDenom n T, chartR n} : Set (R2 n)) := by
      rw [htop]
      exact Submodule.mem_top
    exact hle this
  exact z.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr h1)

/-- The range of the second-chart overlap inclusion equals the range of the localization
map (the overlap isomorphism is bijective). -/
theorem range_overlapToChartInf :
    Set.range (overlapToChartInf n) =
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap (R2 n) (OverlapInf n)))) := by
  rw [overlapToChartInf]
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨((overlapSchemeIso n).hom) w, by rw [Scheme.Hom.comp_apply]⟩
  · rintro ⟨w, rfl⟩
    exact ⟨((overlapSchemeIso n).inv) w, by
      rw [Scheme.Hom.comp_apply]
      simp⟩

/-- COVERAGE of Y_n by the first chart U0 and the open D(q) inside the second chart. -/
theorem cover_point (y : fermatCurveScheme n) :
    y ∈ Set.range (fermatChart0ToCurve n) ∨ y ∈ Set.range (qPiece n T) := by
  haveI : IsOpenImmersion ((fermatTwoChartGlueData n).ι (ULift.up false)) :=
    fermatChart0ToCurve_isOpenImmersion n
  haveI : IsOpenImmersion ((fermatTwoChartGlueData n).ι (ULift.up true)) :=
    fermatChartInfToCurve_isOpenImmersion n
  obtain ⟨i, z, hz⟩ := (fermatTwoChartGlueData n).ι_jointly_surjective y
  cases i with
  | up b =>
    cases b
    · exact Or.inl ⟨z, hz⟩
    · by_cases hq : psiChartInfDenom n T ∈ z.asIdeal
      · left
        have hr : chartR n ∉ z.asIdeal := not_mem_chartR_of_mem_denom n T hq
        obtain ⟨w, hw⟩ := (mem_range_localization_iff n (r1 n) z).mpr hr
        have hzr : z ∈ Set.range (overlapToChartInf n) := by
          rw [range_overlapToChartInf]
          exact ⟨w, hw⟩
        have hzov : z ∈ (overlapToChartInf n).opensRange := by
          rw [Scheme.Hom.mem_opensRange]
          exact hzr
        have hpre := preimage_opensRange_ι (D := fermatTwoChartGlueData n)
          (ULift.up true) (ULift.up false)
        have hzD : z ∈ ((fermatTwoChartGlueData n).f (ULift.up true) (ULift.up false)).opensRange :=
          hzov
        have hzpre : z ∈ ((fermatTwoChartGlueData n).ι (ULift.up true)) ⁻¹ᵁ
            ((fermatTwoChartGlueData n).ι (ULift.up false)).opensRange := by
          rw [hpre]
          exact hzD
        have hmem : ((fermatTwoChartGlueData n).ι (ULift.up true)) z ∈
            ((fermatTwoChartGlueData n).ι (ULift.up false)).opensRange := hzpre
        have hyopen : y ∈ ((fermatTwoChartGlueData n).ι (ULift.up false)).opensRange := by
          rw [← hz]
          exact hmem
        obtain ⟨x, hx⟩ := Scheme.Hom.mem_opensRange.mp hyopen
        exact ⟨x, hx⟩
      · right
        obtain ⟨w, hw⟩ :=
          (mem_range_localization_iff n (psiChartInfDenom n T) z).mpr hq
        refine ⟨w, ?_⟩
        rw [qPiece, Scheme.Hom.comp_apply]
        rw [show (Spec.map (CommRingCat.ofHom
            (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T))))) w = z from hw]
        exact hz

/-- The two open ranges U0 and D(q) cover Y_n. -/
theorem opensRange_sup_top :
    (fermatChart0ToCurve n).opensRange ⊔ (qPiece n T).opensRange = ⊤ := by
  ext y
  simp only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top, Set.mem_union,
    Set.mem_univ, iff_true]
  change y ∈ Set.range (⇑(fermatChart0ToCurve n)) ∨ y ∈ Set.range (⇑(qPiece n T))
  exact cover_point n T y

/-- THE TWO-PIECE OPEN COVER of Y_n used for psi: the first chart U0 and the open D(q)
inside the second chart. -/
noncomputable def psiOpenCover : (fermatCurveScheme n).OpenCover := by
  let X : ULift.{0, 0} Bool → Scheme := fun i => match i with
    | ULift.up false => fermatChart0Scheme n
    | ULift.up true => Spec (CommRingCat.of (Localization.Away (psiChartInfDenom n T)))
  let f : ∀ i, X i ⟶ fermatCurveScheme n := fun i => match i with
    | ULift.up false => fermatChart0ToCurve n
    | ULift.up true => qPiece n T
  haveI : ∀ i, IsOpenImmersion (f i) := by
    intro i
    cases i with
    | up b =>
      cases b
      · dsimp only [f]
        exact fermatChart0ToCurve_isOpenImmersion n
      · dsimp only [f]
        exact qPiece_isOpenImmersion n T
  refine
    { I₀ := ULift.{0, 0} Bool
      X := X
      f := f
      mem₀ := ?_ }
  rw [Scheme.presieve₀_mem_precoverage_iff]
  refine ⟨?_, inferInstance⟩
  intro y
  rcases cover_point n T y with h | h
  · exact ⟨ULift.up false, h⟩
  · exact ⟨ULift.up true, h⟩

instance psiOpenCover_f_false_isOpenImmersion (n : Nat) (T : Finset ℚ) :
    IsOpenImmersion ((psiOpenCover n T).f (ULift.up false)) :=
  fermatChart0ToCurve_isOpenImmersion n

instance psiOpenCover_f_true_isOpenImmersion (n : Nat) (T : Finset ℚ) :
    IsOpenImmersion ((psiOpenCover n T).f (ULift.up true)) :=
  qPiece_isOpenImmersion n T

#print axioms psiOpenCover_f_false_isOpenImmersion
#print axioms psiOpenCover_f_true_isOpenImmersion
#print axioms opensRange_sup_top
#print axioms psiOpenCover
#print axioms cover_point
#print axioms qPiece_isOpenImmersion
#print axioms mem_range_localization_iff
#print axioms range_overlapToChartInf

/-- Projection lemma: the false piece of the cover is the first chart. -/
theorem psiOpenCover_X_false (n : Nat) (T : Finset ℚ) :
    (psiOpenCover n T).X (ULift.up false) = fermatChart0Scheme n := rfl

/-- Projection lemma: the true piece of the cover is the D(q) piece. -/
theorem psiOpenCover_X_true (n : Nat) (T : Finset ℚ) :
    (psiOpenCover n T).X (ULift.up true) =
      Spec (CommRingCat.of (Localization.Away (psiChartInfDenom n T))) := rfl

/-- Projection lemma: the false cover map is the first chart inclusion. -/
theorem psiOpenCover_f_false (n : Nat) (T : Finset ℚ) :
    (psiOpenCover n T).f (ULift.up false) = fermatChart0ToCurve n := rfl

/-- Projection lemma: the true cover map is the D(q) inclusion. -/
theorem psiOpenCover_f_true (n : Nat) (T : Finset ℚ) :
    (psiOpenCover n T).f (ULift.up true) = qPiece n T := rfl

#print axioms psiOpenCover_X_false
#print axioms psiOpenCover_X_true
#print axioms psiOpenCover_f_false
#print axioms psiOpenCover_f_true

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
