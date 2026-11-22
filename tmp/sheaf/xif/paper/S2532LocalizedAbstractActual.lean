import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2532LocalizedAbstractActual
/-- The multiset of orbit sizes (including fixed points). -/
def orbitSizeMultiset {α : Type*} [Fintype α] (σ : Equiv.Perm α) : Multiset ℕ :=
  letI := Classical.decEq α
  σ.cycleType + Multiset.replicate (Fintype.card (Function.fixedPoints σ)) 1
lemma filter_ne_one_add_replicate_count_one (M : Multiset ℕ) :
    M.filter (fun n => n ≠ 1) + Multiset.replicate (M.count 1) 1 = M := by
  classical
  ext n
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
  by_cases hn : n = 1
  · subst hn; simp
  · have h1n : ¬ (1 = n) := fun h => hn h.symm
    simp [hn, h1n]
/-- Localized reduction of an integral polynomial at an ideal. -/
def fbarOf {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : R[X]) : S[X] := f.map φ
/-- The reduced polynomial modulo an ideal. -/
def fbarAt {R : Type*} [CommRing R] (f : R[X]) (p : Ideal R) :
    (R ⧸ p)[X] := f.map (Ideal.Quotient.mk p)
end LeanFormal.IUT.XiFPaper.S2532LocalizedAbstractActual
end
