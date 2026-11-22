import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2535LocalizedIntegralClosureActual
theorem isIntegralClosure_localization
    {A C K L R S : Type*}
    [CommRing A] [CommRing C] [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDomain A] [IsDomain C]
    [Algebra A K] [Algebra A L] [Algebra A C] [Algebra C L] [IsScalarTower A C L]
    [FaithfulSMul A C]
    [IsIntegralClosure C A L] [IsFractionRing C L]
    (M : Submonoid A) (hM : M ≤ nonZeroDivisors A)
    [Algebra A R] [IsLocalization M R] [Algebra A S]
    [Algebra C S] [IsLocalization (Algebra.algebraMapSubmonoid C M) S]
    [Algebra R S] [IsScalarTower A R S] [IsScalarTower A C S]
    [Algebra R L] [Algebra S L] [IsScalarTower A R L] [IsScalarTower C S L]
    [IsScalarTower R S L] :
    IsIntegralClosure S R L := by
  have hACinj : Function.Injective (algebraMap A C) := FaithfulSMul.algebraMap_injective A C
  have hALinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A C L]
    exact (IsFractionRing.injective C L).comp hACinj
  have hM' : Algebra.algebraMapSubmonoid C M ≤ nonZeroDivisors C := by
    rintro y ⟨m, hm, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp (hM hm)) (hACinj (by simpa using h))
  haveI : IsFractionRing S L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (R := C) (M := Algebra.algebraMapSubmonoid C M) S L
  refine IsIntegralClosure.mk ?_ ?_
  · exact IsFractionRing.injective S L
  · intro x
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
        (R := A) M (Rₘ := R) (S := L) x hx
      obtain ⟨c, hc⟩ := (IsIntegralClosure.isIntegral_iff
        (A := C) (R := A) (B := L)).mp hm
      let d : Algebra.algebraMapSubmonoid C M :=
        ⟨algebraMap A C m, ⟨m, m.2, rfl⟩⟩
      refine ⟨IsLocalization.mk' S c d, ?_⟩
      have hspec := congrArg (algebraMap S L) (IsLocalization.mk'_spec S c d)
      simp only [map_mul] at hspec
      have hd : algebraMap S L (algebraMap C S (d : C)) = algebraMap A L m.1 := by
        rw [← IsScalarTower.algebraMap_apply C S L]
        simp [d, IsScalarTower.algebraMap_apply A C L]
      have hcS : algebraMap S L (algebraMap C S c) = algebraMap C L c := by
        rw [IsScalarTower.algebraMap_apply C S L]
      rw [hd, hcS, hc] at hspec
      change algebraMap S L (IsLocalization.mk' S c d) * algebraMap A L m.1 = m.1 • x at hspec
      rw [Algebra.smul_def m.1 x] at hspec
      have hmne : algebraMap A L m.1 ≠ 0 := by
        simpa using hALinj.ne (mem_nonZeroDivisors_iff_ne_zero.mp (hM m.2))
      apply mul_right_cancel₀ hmne
      calc algebraMap S L (IsLocalization.mk' S c d) * algebraMap A L m.1
          = algebraMap A L m.1 * x := hspec
        _ = x * algebraMap A L m.1 := mul_comm _ _
    · rintro ⟨y, rfl⟩
      have hInt : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra (R := A) (A := C) (B := L)
      haveI : Algebra.IsIntegral A C := hInt
      have hmap : IsLocalization.map S (algebraMap A C)
          (show M ≤ (Algebra.algebraMapSubmonoid C M).comap (algebraMap A C) from
            M.le_comap_map) = algebraMap R S := by
        apply IsLocalization.map_unique
        intro a
        rw [← IsScalarTower.algebraMap_apply A R S,
          ← IsScalarTower.algebraMap_apply A C S]
      have h := isIntegral_localization (R := A) (S := C) (M := M)
        (Rₘ := R) (Sₘ := S)
      have hSint : (algebraMap R S).IsIntegral := by
        simpa [hmap] using h
      have hcompRL : (algebraMap S L).comp (algebraMap R S) = algebraMap R L := by
        ext a
        rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R S L]
      show (algebraMap R L).IsIntegralElem (algebraMap S L y)
      rw [← hcompRL]
      exact (hSint y).map (algebraMap S L)
end LeanFormal.IUT.XiFPaper.S2535LocalizedIntegralClosureActual
end
