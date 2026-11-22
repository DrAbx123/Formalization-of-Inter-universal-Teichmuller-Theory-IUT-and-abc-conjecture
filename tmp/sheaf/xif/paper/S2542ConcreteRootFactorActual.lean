import tmp.sheaf.xif.paper.S2541ConcreteRedRootActual
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
open LeanFormal.IUT.XiFPaper.S2541ConcreteRedRootActual
namespace LeanFormal.IUT.XiFPaper.S2542ConcreteRootFactorActual
attribute [local instance] Ideal.Quotient.field
variable (f : R[X]) (p : Ideal R) [hp : p.IsMaximal]
  (P : Ideal S) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
  (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
  (hsplit : (f.map (algebraMap R L)).Splits)
  [DecidableEq (R ⧸ p)] [DecidableEq (S ⧸ P)]
include hmonic in
lemma fbar_ne_zero : fbar f p ≠ 0 :=
  Polynomial.map_monic_ne_zero hmonic
include hmonic in
noncomputable def rootFactorMap :
    (fbar f p).rootSet (S ⧸ P) →
      {g : (R ⧸ p)[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)} :=
  fun y =>
    ⟨minpoly (R ⧸ p) y.1, by
      classical
      rw [Polynomial.mem_normalizedFactors_iff (fbar_ne_zero f p hmonic)]
      have hy := y.2
      rw [mem_rootSet'] at hy
      have hint : IsIntegral (R ⧸ p) y.1 :=
        ⟨fbar f p, Polynomial.Monic.map (Ideal.Quotient.mk p) hmonic, hy.2⟩
      exact ⟨minpoly.irreducible hint, minpoly.monic hint,
        minpoly.dvd _ y.1 hy.2⟩⟩
include hmonic in
lemma rootFactorMap_eq_iff
    (y : (fbar f p).rootSet (S ⧸ P))
    (g : {g : (R ⧸ p)[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}) :
    rootFactorMap (f := f) (p := p) (P := P) (hmonic := hmonic) y = g ↔ y.1 ∈ g.1.rootSet (S ⧸ P) := by
  classical
  constructor
  · intro h
    have hval : g.1 = minpoly (R ⧸ p) y.1 := by
      simpa [rootFactorMap] using congrArg Subtype.val h.symm
    have hgmonic : g.1.Monic := by
      have hgm := g.2
      rw [Polynomial.mem_normalizedFactors_iff (fbar_ne_zero f p hmonic)] at hgm
      exact hgm.2.1
    rw [mem_rootSet']
    constructor
    · rw [hval]
      exact Polynomial.map_monic_ne_zero (hval ▸ hgmonic)
    · rw [hval]
      exact minpoly.aeval _ _
  · intro hroot
    apply Subtype.ext
    have hgmem := g.2
    rw [Polynomial.mem_normalizedFactors_iff (fbar_ne_zero f p hmonic)] at hgmem
    obtain ⟨hgirr, hgmonic, -⟩ := hgmem
    have hroot' := hroot
    rw [mem_rootSet'] at hroot'
    exact (minpoly.eq_of_irreducible_of_monic hgirr hroot'.2 hgmonic).symm

#print axioms rootFactorMap_eq_iff
end LeanFormal.IUT.XiFPaper.S2542ConcreteRootFactorActual
end
