import tmp.sheaf.xif.paper.S2382ArithFrobDoneActual
import tmp.sheaf.xif.paper.S2339FbarFactorsActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2339FbarFactorsActual
namespace LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
attribute [local instance] Ideal.Quotient.field
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (Polynomial.map (algebraMap (RingOfIntegers K) L) f).Splits)
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _

include hp hP hPover hmonic in
theorem s2397Fbar_monic : (fbar f p).Monic := by
  simpa [fbar] using hmonic.map (Ideal.Quotient.mk p)
include hp hP hPover hmonic in
theorem s2397Fbar_ne_zero : fbar f p ≠ 0 := (s2397Fbar_monic f p P hmonic).ne_zero
include hp hP hPover hmonic hsep in
/-- Forward map: a residue root gives its minpoly as a normalized factor. -/
theorem s2397_minpoly_mem_normalizedFactors
    {y : (RingOfIntegers L) ⧸ P}
    (hy : y ∈ (fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :
    minpoly ((RingOfIntegers K) ⧸ p) y ∈
      UniqueFactorizationMonoid.normalizedFactors (fbar f p) := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  have hyroot : (Polynomial.aeval y) (fbar f p) = 0 := by
    rw [Polynomial.mem_rootSet'] at hy
    exact hy.2
  have hint : IsIntegral ((RingOfIntegers K) ⧸ p) y :=
    ⟨fbar f p, s2397Fbar_monic f p P hmonic, hyroot⟩
  rw [Polynomial.mem_normalizedFactors_iff (s2397Fbar_ne_zero f p P hmonic)]
  exact ⟨minpoly.irreducible hint, minpoly.monic hint,
    minpoly.dvd ((RingOfIntegers K) ⧸ p) y hyroot⟩
include hp hP hPover hmonic hsep hsplit in
/-- Backward map: every normalized factor has a residue root with that minpoly. -/
theorem s2397_exists_root_of_normalizedFactor
    {g : ((RingOfIntegers K) ⧸ p)[X]}
    (hg : g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)) :
    ∃ y : (RingOfIntegers L) ⧸ P,
      y ∈ (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) ∧
        minpoly ((RingOfIntegers K) ⧸ p) y = g := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  rw [Polynomial.mem_normalizedFactors_iff (s2397Fbar_ne_zero f p P hmonic)] at hg
  obtain ⟨hg_irr, hg_monic, hg_dvd⟩ := hg
  have hsplitg := s2339Factor_map_splits f p P hmonic hsplit hg_monic hg_dvd
  have hdegpos : 0 < g.natDegree := @Irreducible.natDegree_pos ((RingOfIntegers K) ⧸ p) _ g hg_irr
  have hmap_monic : (g.map (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))).Monic :=
    hg_monic.map _
  have hdegree : (g.map (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hmap_monic.ne_zero,
      Polynomial.natDegree_map_eq_of_injective (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P)).injective]
    exact_mod_cast (show g.natDegree ≠ 0 by omega)
  obtain ⟨y, hy⟩ := hsplitg.exists_eval_eq_zero hdegree
  have hdiv := Polynomial.map_dvd
    (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P)) hg_dvd
  have hybar : (Polynomial.aeval y) (fbar f p) = 0 := by
    rcases hdiv with ⟨q, hq⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hq, Polynomial.eval_mul, hy, zero_mul]
  have hyroot : y ∈ (fbar f p).rootSet ((RingOfIntegers L) ⧸ P) := by
    rw [Polynomial.mem_rootSet']
    exact ⟨(s2397Fbar_monic f p P hmonic).map
      (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P)) |>.ne_zero, hybar⟩
  refine ⟨y, hyroot, ?_⟩
  have hmin := minpoly.eq_of_irreducible hg_irr
    (by simpa [Polynomial.aeval_def] using hy)
  simpa [hg_monic.leadingCoeff] using hmin.symm

end LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
end
