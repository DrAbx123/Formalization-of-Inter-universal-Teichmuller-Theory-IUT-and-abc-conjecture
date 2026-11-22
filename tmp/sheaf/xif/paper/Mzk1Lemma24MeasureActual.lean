import tmp.sheaf.xif.paper.Mzk1Lemma24ConjInvarianceActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24MeasureActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma24GaloisUnionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24UnionActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24ConjInvarianceActual

local instance decEqQbar : DecidableEq Qbar := Classical.decEq Qbar

/-- Conjugate sets are equal on conjugates: if x is conjugate to alpha then the two
conjugate sets coincide (both are the root set of the same minimal polynomial). -/
theorem s3135_conjugateSet_eq_of_mem {α x : Qbar} (hx : x ∈ conjugateSet α) :
    conjugateSet x = conjugateSet α := by
  unfold conjugateSet
  rw [s3135_minpoly_eq_of_mem_conjugateSet hx]

/-- The conjugate closure is idempotent: closing twice adds no new points (paper
[Mzk1] lines 166-169: after replacing S by the Galois-stable set, the set is stable). -/
theorem s3135_pointClosure_idem (S : Finset Qbar) :
    pointClosure (pointClosure S) = pointClosure S := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [pointClosure, Finset.mem_biUnion] at hx
    obtain ⟨β, hβ, hxβ⟩ := hx
    rw [pointClosure, Finset.mem_biUnion] at hβ
    obtain ⟨α, hα, hβα⟩ := hβ
    rw [Set.Finite.mem_toFinset] at hxβ hβα
    have heq : conjugateSet β = conjugateSet α := s3135_conjugateSet_eq_of_mem hβα
    rw [heq] at hxβ
    rw [pointClosure, Finset.mem_biUnion]
    exact ⟨α, hα, by rw [Set.Finite.mem_toFinset]; exact hxβ⟩
  · exact s3135_subset_pointClosure (pointClosure S)

/-- m(S-bar) = m(S): replacing S by its Galois-conjugate closure does not change the
maximum reduced degree (paper lines 166-169 preparation of the induction). -/
theorem s3135_mOfPoints_pointClosure_eq (S : Finset Qbar) (hne : S.Nonempty) :
    mOfPoints (pointClosure S) (hne.mono (s3135_subset_pointClosure S)) =
      mOfPoints S hne := by
  have hneC : (pointClosure S).Nonempty := hne.mono (s3135_subset_pointClosure S)
  have hC := (Finset.max'_eq_iff
    (s := (pointClosure S).image reducedDegreeOfPoint)
    (H := hneC.image reducedDegreeOfPoint)
    (mOfPoints (pointClosure S) hneC)).mp rfl
  have hS := (Finset.max'_eq_iff
    (s := S.image reducedDegreeOfPoint)
    (H := hne.image reducedDegreeOfPoint)
    (mOfPoints S hne)).mp rfl
  apply le_antisymm
  · unfold mOfPoints
    rw [Finset.max'_le_iff]
    intro b hb
    rw [s3135_image_pointClosure_eq S] at hb
    exact hS.2 b hb
  · unfold mOfPoints
    rw [Finset.max'_le_iff]
    intro b hb
    exact hC.2 b (by rw [s3135_image_pointClosure_eq S]; exact hb)

/-- d-monotonicity: if S subset T and the maximum reduced degree m is the same, then
d(S) <= d(T) (each filtering point of S is a filtering point of T with the same
contribution). -/
theorem s3135_dOfPoints_mono (S T : Finset Qbar) (hST : S ⊆ T)
    (hneS : S.Nonempty) (hneT : T.Nonempty)
    (hm : mOfPoints S hneS = mOfPoints T hneT) :
    dOfPoints S hneS ≤ dOfPoints T hneT := by
  unfold dOfPoints
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro α hα
    rw [Finset.mem_filter] at hα ⊢
    exact ⟨hST hα.1, by rw [hα.2, hm]⟩
  · intro α hαT hαnot
    exact Nat.zero_le _

/-- Status: (G) tail complete: conjugation invariance, closure idempotence,
m(S-bar)=m(S), and d-monotonicity under subset with equal m. -/
def s3135Mzk1MeasureStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.measure-monotonicity"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 166-206"
    status := Audit.VerificationStatus.interface
    note := "PROVED: conjugate sets equal on conjugates; conjugate closure idempotent; m(S-bar)=m(S) (via Finset.max'_eq_iff characterization transfer + max'_le on the image equality); d-monotonicity (S subset T with equal m => d(S) <= d(T)). REMAINING: (F) f0 coefficient bound d0^d0 (lines 183-199), (D) descent (159-160), (M) main statement (144-160) with P^1-morphism language gap to be named. No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.conj-invariance" ]
    sorryItems := [ "(F) f0 coefficient bound", "(D) descent", "(M) main statement" ] }

#check s3135_mOfPoints_pointClosure_eq
#check s3135_dOfPoints_mono
#check s3135_pointClosure_idem
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24MeasureActual
end