import tmp.sheaf.xif.paper.S2853ChartYNegationActual
import tmp.sheaf.xif.paper.S2820E37TransitionActual
import Mathlib.AlgebraicGeometry.Cover.Open

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2853ChartYNegationActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2855ChartYOpenCoverActual


variable (K : Type) [Field K]

abbrev tY : E37ChartYRing K := S2853ChartYT K

/-- The two chart-Y affine pieces: D(1+t) and D(t). -/
noncomputable def chartYOpenCoverObj (i : Fin 2) : Scheme :=
  if i = 0 then Spec (CommRingCat.of (S2853ChartYNegRing K))
  else Spec (CommRingCat.of (Localization.Away (tY K)))

noncomputable def chartYOpenCoverMap (i : Fin 2) :
    chartYOpenCoverObj K i ⟶ E37ChartYScheme K := by
  by_cases h : i = 0
  · subst h
    change Spec (CommRingCat.of (S2853ChartYNegRing K)) ⟶
      Spec (CommRingCat.of (E37ChartYRing K))
    exact Spec.map (CommRingCat.ofHom
      (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)))
  · have hi : i = 1 := by fin_cases i <;> simp_all
    subst hi
    change Spec (CommRingCat.of (Localization.Away (tY K))) ⟶
      Spec (CommRingCat.of (E37ChartYRing K))
    exact Spec.map (CommRingCat.ofHom
      (algebraMap (E37ChartYRing K) (Localization.Away (tY K))))

theorem chartYOpenCover_covers :
    ∀ x : E37ChartYScheme K, ∃ i y, chartYOpenCoverMap K i y = x := by
  intro x
  by_cases h : (1 + tY K) ∈ x.asIdeal
  · have ht : tY K ∉ x.asIdeal := by
      intro ht
      have h1 : (1 : E37ChartYRing K) ∈ x.asIdeal := by
        have := x.asIdeal.sub_mem h ht
        simpa using this
      exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem x.asIdeal h1 isUnit_one)
    have hxr : x ∈ Set.range (chartYOpenCoverMap K 1) := by
      change x ∈ Set.range (Spec.map (CommRingCat.ofHom
        (algebraMap (E37ChartYRing K) (Localization.Away (tY K)))))
      rw [show Set.range (Spec.map (CommRingCat.ofHom
          (algebraMap (E37ChartYRing K) (Localization.Away (tY K))))) =
          (PrimeSpectrum.basicOpen (tY K) : Set (PrimeSpectrum (E37ChartYRing K))) from
        PrimeSpectrum.localization_away_comap_range (Localization.Away (tY K)) (tY K)]
      exact (PrimeSpectrum.mem_basicOpen _ _).mpr ht
    exact ⟨1, hxr.choose, hxr.choose_spec⟩
  · have h1t : (1 + tY K) ∉ x.asIdeal := h
    have hxr : x ∈ Set.range (chartYOpenCoverMap K 0) := by
      change x ∈ Set.range (Spec.map (CommRingCat.ofHom
        (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K))))
      rw [show Set.range (Spec.map (CommRingCat.ofHom
          (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)))) =
          (PrimeSpectrum.basicOpen (1 + tY K) : Set (PrimeSpectrum (E37ChartYRing K))) from
        PrimeSpectrum.localization_away_comap_range (S2853ChartYNegRing K) (1 + tY K)]
      exact (PrimeSpectrum.mem_basicOpen _ _).mpr h1t
    exact ⟨0, hxr.choose, hxr.choose_spec⟩


theorem chartYOpenCoverMap_eq0 :
    chartYOpenCoverMap K 0 = Spec.map (CommRingCat.ofHom
      (algebraMap (E37ChartYRing K) (S2853ChartYNegRing K))) := by
  unfold chartYOpenCoverMap
  rw [dif_pos rfl]

theorem chartYOpenCoverMap_eq1 :
    chartYOpenCoverMap K 1 = Spec.map (CommRingCat.ofHom
      (algebraMap (E37ChartYRing K) (Localization.Away (tY K)))) := by
  unfold chartYOpenCoverMap
  rw [dif_neg (by decide : (1 : Fin 2) ≠ 0)]

theorem chartYOpenCoverMap_isOpen0 :
    IsOpenImmersion (chartYOpenCoverMap K 0) := by
  rw [chartYOpenCoverMap_eq0]
  exact Scheme.isOpenImmersion_SpecMap_localizationAway (1 + tY K)

theorem chartYOpenCoverMap_isOpen1 :
    IsOpenImmersion (chartYOpenCoverMap K 1) := by
  rw [chartYOpenCoverMap_eq1]
  exact Scheme.isOpenImmersion_SpecMap_localizationAway (tY K)

noncomputable def chartYOpenCover : (E37ChartYScheme K).OpenCover where
  I₀ := Fin 2
  X := chartYOpenCoverObj K
  f := chartYOpenCoverMap K
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · exact chartYOpenCover_covers K
    · intro i
      fin_cases i
      · exact chartYOpenCoverMap_isOpen0 K
      · exact chartYOpenCoverMap_isOpen1 K

#check chartYOpenCover
#print axioms chartYOpenCover

end LeanFormal.IUT.XiFPaper.S2855ChartYOpenCoverActual
end