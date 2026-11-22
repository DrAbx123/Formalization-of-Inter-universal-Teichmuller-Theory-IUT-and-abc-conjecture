import tmp.sheaf.xif.paper.S2545ConcreteFiberCardActual
import tmp.sheaf.xif.paper.S2532LocalizedDefinitionsActual
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2541ConcreteRedRootActual
open LeanFormal.IUT.XiFPaper.S2542ConcreteRootFactorActual
open LeanFormal.IUT.XiFPaper.S2544ConcretePermBarInvariantActual
open LeanFormal.IUT.XiFPaper.S2545ConcreteFiberCardActual
namespace LeanFormal.IUT.XiFPaper.S2546ConcreteCycleTypeActualAdapted
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
attribute [local instance] Ideal.Quotient.field
lemma univ_val_attach {α : Type*} [DecidableEq α] (s : Multiset α) :
    (Finset.univ : Finset {x // x ∈ s}).val = s.attach := by
  have h : (Finset.univ : Finset {x // x ∈ s}) = s.attach.toFinset := rfl
  rw [h, Multiset.toFinset_val, Multiset.Nodup.dedup]
  exact (Multiset.nodup_attach).mpr s.nodup
lemma normalize_attach {α : Type*} [DecidableEq α] (s : Multiset α) (d : α → ℕ)
    (hd : ∀ x ∈ s, 1 ≤ d x) :
    (s.attach.filter (fun x => 2 ≤ d x.1)).map (fun x => d x.1) =
      (s.map d).filter (fun n => n ≠ 1) := by
  have hmap : s.map d = s.attach.map (fun x => d x.1) := by
    rw [← Multiset.attach_map_val s, Multiset.map_map]
    rfl
  rw [hmap, ← Multiset.filter_map]
  congr 1
  ext x
  simp only [Function.comp_apply]
  constructor
  · intro h
    have h1 := hd x.1 x.2
    omega
  · intro h
    have h1 := hd x.1 x.2
    omega
variable (f : R[X]) (p : Ideal R) [hp : p.IsMaximal]
  (P : Ideal S) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
  (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
  (hsplit : (f.map (algebraMap R L)).Splits)
  [Fintype (R ⧸ p)] [Fintype (S ⧸ P)]
  [DecidableEq (R ⧸ p)] [DecidableEq (S ⧸ P)]
include hmonic hsep hsplit in
theorem concrete_permBar_cycleType :
    (permBar (f := f) (p := p) (P := P)).cycleType =
      (LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual.factorDegrees (fbar f p)).filter
        (fun n => n ≠ 1) := by
  rw [concrete_permBar_cycleType_fiber]
  rw [LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual.factorDegrees]
  change (Finset.univ.filter (fun g : {g : (R ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)} =>
      2 ≤ g.1.natDegree)).val.map (fun g => g.1.natDegree) =
    ((UniqueFactorizationMonoid.normalizedFactors (fbar f p)).map Polynomial.natDegree).filter
      (fun n => n ≠ 1)
  rw [show (Finset.univ.filter (fun g : {g : (R ⧸ p)[X] //
      g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)} =>
      2 ≤ g.1.natDegree)).val =
    ((UniqueFactorizationMonoid.normalizedFactors (fbar f p)).attach.filter
      (fun g => 2 ≤ g.1.natDegree)) from by
    rw [Finset.filter_val, univ_val_attach]]
  exact normalize_attach _ _ (by
    intro g hg
    rw [Polynomial.mem_normalizedFactors_iff (fbar_ne_zero f p hmonic)] at hg
    obtain ⟨hgirr, hgmonic, -⟩ := hg
    have hpos : 0 < g.natDegree := (hgmonic.natDegree_pos).mpr hgirr.ne_one
    omega)
#print axioms concrete_permBar_cycleType
end LeanFormal.IUT.XiFPaper.S2546ConcreteCycleTypeActualAdapted
end
