import tmp.sheaf.xif.paper.S2542ConcreteRootFactorActual
import tmp.sheaf.xif.paper.S2543FrobeniusOrbitActual
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2541ConcreteRedRootActual
open LeanFormal.IUT.XiFPaper.S2542ConcreteRootFactorActual
namespace LeanFormal.IUT.XiFPaper.S2544ConcretePermBarInvariantActual
attribute [local instance] Ideal.Quotient.field
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
variable (f : R[X]) (p : Ideal R) [hp : p.IsMaximal]
  (P : Ideal S) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
  (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
  (hsplit : (f.map (algebraMap R L)).Splits)
  [Fintype (R ⧸ p)] [Fintype (S ⧸ P)]
  [DecidableEq (R ⧸ p)] [DecidableEq (S ⧸ P)]
lemma permBar_apply_val (y : (fbar f p).rootSet (S ⧸ P)) :
    ((permBar (f := f) (p := p) (P := P) y).1) =
      frobBar (p := p) (P := P) y.1 := by
  simp [permBar, Equiv.ofBijective]
lemma rootFactorMap_permBar (y : (fbar f p).rootSet (S ⧸ P)) :
    rootFactorMap (f := f) (p := p) (P := P) (hmonic := hmonic)
      (permBar (f := f) (p := p) (P := P) y) =
    rootFactorMap (f := f) (p := p) (P := P) (hmonic := hmonic) y := by
  classical
  apply Subtype.ext
  change minpoly (R ⧸ p) (((permBar (f := f) (p := p) (P := P)) y).1) =
    minpoly (R ⧸ p) y.1
  rw [permBar_apply_val f p P]
  set g : (R ⧸ p)[X] := minpoly (R ⧸ p) y.1 with hg
  have hyroot : y.1 ∈ (fbar f p).rootSet (S ⧸ P) := y.2
  have hint : IsIntegral (R ⧸ p) y.1 :=
    ⟨fbar f p, Polynomial.Monic.map (Ideal.Quotient.mk p) hmonic, by
      rw [mem_rootSet'] at hyroot; exact hyroot.2⟩
  have hgirr : Irreducible g := by rw [hg]; exact minpoly.irreducible hint
  have hgmonic : g.Monic := by rw [hg]; exact minpoly.monic hint
  have hyg : y.1 ∈ g.rootSet (S ⧸ P) := by
    rw [mem_rootSet']
    exact ⟨Polynomial.map_monic_ne_zero hgmonic, minpoly.aeval _ _⟩
  have hfrob := LeanFormal.IUT.XiFPaper.S2543FrobeniusOrbitActual.frobenius_mem_roots
    (p := p) (P := P) g hgirr hgmonic y.1 hyg
  rw [mem_rootSet'] at hfrob
  exact (minpoly.eq_of_irreducible_of_monic hgirr hfrob.2 hgmonic).symm

#print axioms rootFactorMap_permBar
end LeanFormal.IUT.XiFPaper.S2544ConcretePermBarInvariantActual
end
