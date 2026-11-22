import Mathlib
noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2547NormalizeActual
lemma univ_val_attach {α : Type*} [DecidableEq α] (s : Multiset α) (hs : s.Nodup) :
    (Finset.univ : Finset {x // x ∈ s}).val = s.attach := by
  have hnd : s.attach.Nodup := (Multiset.nodup_attach).mpr hs
  have h : (Finset.univ : Finset {x // x ∈ s}) = s.attach.toFinset := rfl
  rw [h, Multiset.toFinset_val, hnd.dedup]
lemma normalize_attach {α : Type*} [DecidableEq α] (s : Multiset α) (d : α → ℕ)
    (hd : ∀ x ∈ s, 1 ≤ d x) :
    (s.attach.filter (fun x => 2 ≤ d x.1)).map (fun x => d x.1) =
      (s.map d).filter (fun n => n ≠ 1) := by
  have hmap : s.map d = s.attach.map (fun x => d x.1) := by
    rw [← Multiset.attach_map_val s, Multiset.map_map]
    simp
  have hfm := Multiset.filter_map (p := fun n : ℕ => n ≠ 1)
    (f := fun x : {x // x ∈ s} => d x.1) s.attach
  rw [hmap, hfm]
  congr 1
  apply Multiset.filter_congr
  intro x hx
  simp only [Function.comp_apply]
  have h1 := hd x.1 x.2
  omega
#print axioms univ_val_attach
#print axioms normalize_attach
end LeanFormal.IUT.XiFPaper.S2547NormalizeActual
end
