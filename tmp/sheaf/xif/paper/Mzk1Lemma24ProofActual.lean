import Mathlib
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24ProofActual

/-- The reduced degree of a number field F (paper [Mzk1] line 170): [F : Q] - 1. -/
def reducedDegree (F : Type) [Field F] [NumberField F] : Nat := Module.finrank ℚ F - 1

/-- The base field has reduced degree 0 (paper: S subset P^1(Q) iff m(S)=0). -/
theorem s3135_reducedDegree_rat : reducedDegree ℚ = 0 := by
  simp [reducedDegree]

/-- m(S) (paper [Mzk1] lines 171-174): the maximum of the reduced degrees of the
fields of definition of the points of S. -/
def mOfDegrees (degs : Finset Nat) (hne : degs.Nonempty) : Nat := degs.max' hne

/-- d(S) (paper lines 175-178): the sum of the reduced degrees equal to m(S). -/
def dOfDegrees (degs : Finset Nat) (hne : degs.Nonempty) : Nat :=
  ∑ n ∈ degs.filter (fun n => n = mOfDegrees degs hne), n

/-- Paper lines 177-178: d(S) = 0 if and only if m(S) = 0. -/
theorem s3135_dOfDegrees_eq_zero_iff (degs : Finset Nat) (hne : degs.Nonempty) :
    dOfDegrees degs hne = 0 ↔ mOfDegrees degs hne = 0 := by
  constructor
  · intro h
    have hm : mOfDegrees degs hne ∈ degs.filter (fun n => n = mOfDegrees degs hne) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.max'_mem degs hne, rfl⟩
    have hle : mOfDegrees degs hne ≤ dOfDegrees degs hne := by
      unfold dOfDegrees
      exact Finset.single_le_sum (f := fun n => n) (fun _ _ => Nat.zero_le _) hm
    omega
  · intro h
    unfold dOfDegrees
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_filter] at hn
    have hnle : n ≤ mOfDegrees degs hne := Finset.le_max' degs n hn.1
    omega

/-- The nested-induction measure of Lemma 2.4's proof (lines 179-206): lexicographic
order on the pair (m(S), d(S)). -/
def lemma24Measure : Nat × Nat → Nat × Nat → Prop := Prod.Lex (· < ·) (· < ·)

/-- The nested (m(S), d(S))-induction is well-founded (paper line 179). -/
theorem s3135_lemma24Measure_wf : WellFounded lemma24Measure :=
  WellFounded.prod_lex wellFounded_lt wellFounded_lt

/-- Reduction-step compatibility: either m(S') < m(S), or m(S') = m(S) and
d(S') < d(S), strictly decreases the measure. -/
theorem s3135_lemma24Measure_step {m d m' d' : Nat}
    (h : m' < m ∨ (m' = m ∧ d' < d)) : lemma24Measure (m', d') (m, d) :=
  Prod.lex_def.mpr h

/-- Status of the full Lemma 2.4 proof: arithmetic layer proved here; geometric and
descent steps named class-B inputs. -/
def s3135Mzk1Lemma24Status : Audit.Obligation :=
  { id := "MZK1.lemma24.reduced-degree-induction"
    source :=
      "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 " ++
        "(lines 144-206); Mzk1Lemma24InductionActual (5-row statement ledger); " ++
        "Mzk1Section2StatementsActual/Mzk1Section3StatementsActual"
    status := Audit.VerificationStatus.interface
    note :=
      "PROVED HERE (class A): reducedDegree F = [F:Q]-1 (line 170); m(S)=max of " ++
        "reduced degrees (171-174); d(S)=sum of the reduced degrees equal to m(S) " ++
        "(175-178); s3135_dOfDegrees_eq_zero_iff = paper d(S)=0 iff m(S)=0; " ++
        "s3135_lemma24Measure_wf = well-foundedness of the nested (m,d)-lex " ++
        "induction (line 179); s3135_lemma24Measure_step = reduction-step " ++
        "compatibility (lines 200-203).  REMAINING class-B steps, exactly: " ++
        "(i) Galois-conjugate union closure (lines 166-169); (ii) f0-normalization " ++
        "and coefficient bound |coeffs| <= d0^d0 (lines 183-199); (iii) main " ++
        "statement (144-160) with descent to F (lines 159-160).  No fake witnesses; " ++
        "no registry edit (frozen 14041)."
    dependsOn := [ "GENELL.P2.mzk1-statements", "GENELL.P0" ]
    sorryItems :=
      [ "Galois-conjugate union closure (Mzk1 lines 166-169)",
        "f0 coefficient bound d0^d0 (lines 187-199)",
        "descent to F (lines 159-160)",
        "main Lemma 2.4 conclusion (lines 144-160)" ] }

#check reducedDegree
#check s3135_dOfDegrees_eq_zero_iff
#check s3135_lemma24Measure_wf
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24ProofActual
end
-- bump-mzk1-1