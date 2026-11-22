import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2533LocalizedDedekindActual
/-- Nonmonic root count over a field: no monicity needed. -/
theorem nonmonic_card_rootSet
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : K[X]) (hf : f ≠ 0) (hsep : f.Separable)
    (hsplit : (f.map (algebraMap K L)).Splits) :
    Fintype.card (f.rootSet L) = f.natDegree :=
  Polynomial.card_rootSet_eq_natDegree hsep hsplit
/-- Splitting over the integral closure S of R in L, for a monic polynomial. -/
theorem splits_over_integralClosure
    {R S L : Type*} [CommRing R] [CommRing S] [Field L]
    [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L]
    [FaithfulSMul R L] [IsDomain S]
    [IsIntegralClosure S R L]
    (f : R[X]) (hmonic : f.Monic)
    (hsplit : (f.map (algebraMap R L)).Splits) :
    (f.map (algebraMap R S)).Splits := by
  have hmap : f.map (algebraMap R L) =
      (f.map (algebraMap R S)).map (algebraMap S L) := by
    rw [Polynomial.map_map, IsScalarTower.algebraMap_eq R S L]
  refine Polynomial.Splits.of_splits_map_of_injective
    (f := f.map (algebraMap R S)) (i := algebraMap S L)
    (IsIntegralClosure.algebraMap_injective S R L) ?_ ?_
  · rw [← hmap]; exact hsplit
  · intro a ha
    rw [← hmap] at ha
    have hfne : f.map (algebraMap R L) ≠ 0 :=
      Polynomial.map_monic_ne_zero hmonic
    have hroot : aeval a f = 0 := by
      rw [mem_roots hfne] at ha
      simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using ha
    have hint : IsIntegral R a := ⟨f, hmonic, hroot⟩
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff
      (A := S) (R := R) (B := L)).mp hint
    exact ⟨y, hy⟩
#print axioms nonmonic_card_rootSet
#print axioms splits_over_integralClosure
end LeanFormal.IUT.XiFPaper.S2533LocalizedDedekindActual
end
