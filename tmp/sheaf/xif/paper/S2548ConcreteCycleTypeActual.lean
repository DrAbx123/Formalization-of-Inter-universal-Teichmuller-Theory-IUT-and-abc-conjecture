import tmp.sheaf.xif.paper.S2547NormalizeActual
import tmp.sheaf.xif.paper.S2545ConcreteFiberCardActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2541ConcreteRedRootActual
open LeanFormal.IUT.XiFPaper.S2542ConcreteRootFactorActual
open LeanFormal.IUT.XiFPaper.S2544ConcretePermBarInvariantActual
open LeanFormal.IUT.XiFPaper.S2545ConcreteFiberCardActual
open LeanFormal.IUT.XiFPaper.S2547NormalizeActual
namespace LeanFormal.IUT.XiFPaper.S2548ConcreteCycleTypeActual
attribute [local instance] Ideal.Quotient.field
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual

variable (f : R[X]) (p : Ideal R) [hp : p.IsMaximal]
  (P : Ideal S) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
  (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
  (hsplit : (f.map (algebraMap R L)).Splits)
  [Fintype (R ⧸ p)] [Fintype (S ⧸ P)]
  [DecidableEq (R ⧸ p)] [DecidableEq (S ⧸ P)]

include hmonic hsep hsplit in
theorem concrete_permBar_cycleType :
    (permBar (f := f) (p := p) (P := P)).cycleType =
      (LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.factorDegrees (fbar f p)).filter
        (fun n => n ≠ 1) := by
  classical
  letI hdec : DecidableEq (R ⧸ p) := Classical.decEq _
  let s : Multiset ((R ⧸ p)[X]) := UniqueFactorizationMonoid.normalizedFactors (fbar f p)
  have hfbar_ne : fbar f p ≠ 0 := fbar_ne_zero f p hmonic
  have hsquare : Squarefree (fbar f p) := hsep.squarefree
  have hrad : IsRadical (fbar f p) :=
    (isRadical_iff_squarefree_of_ne_zero (R := (R ⧸ p)[X]) hfbar_ne).mpr hsquare
  have hnodup : s.Nodup := UniqueFactorizationMonoid.normalizedFactors_nodup hrad
  have hd : ∀ x ∈ s, 1 ≤ x.natDegree := by
    intro x hx
    rw [Polynomial.mem_normalizedFactors_iff hfbar_ne] at hx
    obtain ⟨hirr, hmon, hdvd⟩ := hx
    exact Nat.succ_le_of_lt (Irreducible.natDegree_pos hirr)
  calc
    (permBar (f := f) (p := p) (P := P)).cycleType
        = (Finset.univ.filter
            (fun g : {g : (R ⧸ p)[X] // g ∈ s} => 2 ≤ g.1.natDegree)).val.map
            (fun g => g.1.natDegree) := by
          simpa [s] using concrete_permBar_cycleType_fiber (f := f) (p := p) (P := P)
            (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)
    _ = (s.attach.filter (fun g => 2 ≤ g.1.natDegree)).map (fun g => g.1.natDegree) := by
          rw [Finset.filter_val, univ_val_attach s hnodup]
    _ = (s.map (fun g => g.natDegree)).filter (fun n => n ≠ 1) := by
          exact normalize_attach s (fun g => g.natDegree) hd
    _ = (LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.factorDegrees
          (fbar f p)).filter (fun n => n ≠ 1) := by
          simp [s, LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.factorDegrees]

#print axioms concrete_permBar_cycleType

end LeanFormal.IUT.XiFPaper.S2548ConcreteCycleTypeActual
end