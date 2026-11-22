import tmp.sheaf.xif.paper.S2330FrobCardsActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2339FbarFactorsActual
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2318FrobTransitiveActual
open LeanFormal.IUT.XiFPaper.S2330FrobCardsActual
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
include hp hP hPover hmonic hsplit in
/-- fbar splits after scalar extension to the residue field of L. -/
theorem s2339FbarMap_splits :
    ((fbar f p).map (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))).Splits := by
  have h1 := Polynomial.Splits.map (splits_over_ringOfIntegers f p P hmonic hsplit)
    (Ideal.Quotient.mk P)
  rw [Polynomial.map_map] at h1
  convert h1 using 1
  rw [fbar, Polynomial.map_map]
  congr 1
include hp hP hPover hsep in
/-- A factor of fbar is separable. -/
theorem s2339Factor_separable
    {g : ((RingOfIntegers K) ⧸ p)[X]} (hg_dvd : g ∣ fbar f p) :
    g.Separable :=
  hsep.of_dvd hg_dvd
include hp hP hPover hmonic hsplit in
/-- A monic factor of fbar splits after scalar extension. -/
theorem s2339Factor_map_splits
    {g : ((RingOfIntegers K) ⧸ p)[X]} (hg : g.Monic)
    (hg_dvd : g ∣ fbar f p) :
    (g.map (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))).Splits := by
  have hfbar : ((fbar f p).map
      (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))).Splits :=
    s2339FbarMap_splits f p P hmonic hsplit
  have hfbar_ne : ((fbar f p).map
      (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))) ≠ 0 :=
    ((hmonic.map (Ideal.Quotient.mk p)).map
      (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))).ne_zero
  have hdiv := Polynomial.map_dvd
    (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P)) hg_dvd
  exact Polynomial.Splits.of_dvd hfbar hfbar_ne hdiv
include hp hP hPover hmonic hsep hsplit in
/-- Unconditional q-Frobenius transitivity on the roots of a monic
irreducible factor of fbar. -/
theorem s2339FrobTransitive
    {g : ((RingOfIntegers K) ⧸ p)[X]} (hg : g.Monic) (hirr : Irreducible g)
    (hg_dvd : g ∣ fbar f p)
    {x y : (RingOfIntegers L) ⧸ P} (hx : aeval x g = 0) (hy : aeval y g = 0) :
    ∃ n : ℕ, (frobBar p P)^[n] x = y :=
  s2330FrobTransitive_of_splits_separable p P hg hirr
    (s2339Factor_separable f p P hsep hg_dvd)
    (s2339Factor_map_splits f p P hmonic hsplit hg hg_dvd) hx hy
#print axioms s2339FbarMap_splits
#print axioms s2339Factor_separable
#print axioms s2339Factor_map_splits
#print axioms s2339FrobTransitive
end LeanFormal.IUT.XiFPaper.S2339FbarFactorsActual
end
