import tmp.sheaf.xif.paper.S2397RootFactorMapActual
import tmp.sheaf.xif.paper.S2330FrobCardsActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2330FrobCardsActual
open LeanFormal.IUT.XiFPaper.S2339FbarFactorsActual
namespace LeanFormal.IUT.XiFPaper.S2408FiberSizesActual
attribute [local instance] Ideal.Quotient.field
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (Polynomial.map (algebraMap (RingOfIntegers K) L) f).Splits)
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _
/-- Roots whose minpoly is g. -/
def s2408FiberSet (g : ((RingOfIntegers K) ⧸ p)[X]) : Set ((RingOfIntegers L) ⧸ P) :=
  {y | minpoly ((RingOfIntegers K) ⧸ p) y = g}
include hp hP hPover hmonic hsep in
theorem s2408FiberSet_eq_rootSet
    {g : ((RingOfIntegers K) ⧸ p)[X]} (hg_monic : g.Monic) (hg_irr : Irreducible g) :
    s2408FiberSet (K := K) (L := L) (p := p) (P := P) g =
      g.rootSet ((RingOfIntegers L) ⧸ P) := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  ext y
  constructor
  · intro hy
    rw [Polynomial.mem_rootSet']
    have hroot : (Polynomial.aeval y) g = 0 := by
      rw [show g = minpoly ((RingOfIntegers K) ⧸ p) y from hy.symm]
      exact minpoly.aeval _ _
    exact ⟨(hg_monic.map (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))).ne_zero, hroot⟩
  · intro hy
    rw [Polynomial.mem_rootSet'] at hy
    exact (minpoly.eq_of_irreducible hg_irr hy.2).symm |>.trans (by simp [hg_monic.leadingCoeff])
include hp hP hPover hmonic in
theorem s2408FiberSet_ncard
    (hsep : (fbar f p).Separable)
    (hsplit : (Polynomial.map (algebraMap (RingOfIntegers K) L) f).Splits)
    {g : ((RingOfIntegers K) ⧸ p)[X]}
    (hg : g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)) :
    (s2408FiberSet (K := K) (L := L) (p := p) (P := P) g).ncard = g.natDegree := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  rw [Polynomial.mem_normalizedFactors_iff (s2397Fbar_ne_zero f p P hmonic)] at hg
  obtain ⟨hg_irr, hg_monic, hg_dvd⟩ := hg
  rw [s2408FiberSet_eq_rootSet (K := K) (L := L) (f := f) (hmonic := hmonic)
    (hsep := hsep) (p := p) (P := P) (hg_monic := hg_monic) (hg_irr := hg_irr)]
  have hsepg : g.Separable :=
    s2339Factor_separable (K := K) (L := L) (f := f) (p := p) (P := P)
      (g := g) (hsep := hsep) (hg_dvd := hg_dvd)
  have hsplitg : (g.map (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))).Splits :=
    s2339Factor_map_splits (K := K) (L := L) (f := f) (p := p) (P := P)
      (g := g) (hmonic := hmonic) (hsplit := hsplit)
      (hg := hg_monic) (hg_dvd := hg_dvd)
  have hcard := Polynomial.card_rootSet_eq_natDegree (F := ((RingOfIntegers K) ⧸ p)) (K := ((RingOfIntegers L) ⧸ P)) hsepg hsplitg
  simpa using hcard
include hp hP hPover hmonic in
theorem s2408FiberSizes_eq_factorDegrees
    (hsep : (fbar f p).Separable)
    (hsplit : (Polynomial.map (algebraMap (RingOfIntegers K) L) f).Splits) :
    (UniqueFactorizationMonoid.normalizedFactors (fbar f p)).map
      (fun g => (s2408FiberSet (K := K) (L := L) (p := p) (P := P) g).ncard) =
      factorDegrees (fbar f p) := by
  classical
  unfold factorDegrees
  apply Multiset.map_congr rfl
  intro g hg
  exact s2408FiberSet_ncard (K := K) (L := L) (f := f) (hmonic := hmonic)
    (hsep := hsep) (hsplit := hsplit) (p := p) (P := P) (hg := hg)
#print axioms s2408FiberSet_eq_rootSet
#print axioms s2408FiberSet_ncard
#print axioms s2408FiberSizes_eq_factorDegrees
end LeanFormal.IUT.XiFPaper.S2408FiberSizesActual
end
