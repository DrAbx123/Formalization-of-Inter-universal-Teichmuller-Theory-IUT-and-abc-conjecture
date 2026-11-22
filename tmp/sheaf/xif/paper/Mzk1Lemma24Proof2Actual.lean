import tmp.sheaf.xif.paper.Mzk1Lemma24ProofActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24Proof2Actual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma24ProofActual

/-- Reduced degree zero is equivalent to [F:Q] = 1 (paper line 170-178 context). -/
theorem s3135_reducedDegree_eq_zero_iff {F : Type} [Field F] [NumberField F] :
    reducedDegree F = 0 ↔ Module.finrank ℚ F = 1 := by
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  unfold reducedDegree
  omega

/-- m(S) = 0 iff every reduced degree in the degree set is 0 (paper line 177-178,
first equivalence). -/
theorem s3135_mOfDegrees_eq_zero_iff (degs : Finset Nat) (hne : degs.Nonempty) :
    mOfDegrees degs hne = 0 ↔ ∀ n ∈ degs, n = 0 := by
  constructor
  · intro h n hn
    have hle : n ≤ mOfDegrees degs hne := Finset.le_max' degs n hn
    omega
  · intro h
    have hle : mOfDegrees degs hne ≤ 0 := by
      unfold mOfDegrees
      rw [Finset.max'_le_iff]
      intro n hn
      have := h n hn
      omega
    omega

/-- The nested strong induction principle on the measure (m(S), d(S)): this is the
exact induction scheme used by the paper's Lemma 2.4 proof (lines 179-206), supplied
by well-foundedness of the lexicographic measure. -/
theorem s3135_lemma24_induction {P : Nat × Nat → Prop}
    (h : ∀ md : Nat × Nat, (∀ md' : Nat × Nat, lemma24Measure md' md → P md') → P md) :
    ∀ md : Nat × Nat, P md :=
  fun md => s3135_lemma24Measure_wf.induction (C := P) md h

/-- Combined arithmetic content of Lemma 2.4 lines 170-178: reduced degrees are
nonnegative; d(S)=0 iff m(S)=0; m(S)=0 iff all reduced degrees vanish. -/
theorem s3135_lemma24_arithmetic_layer (degs : Finset Nat) (hne : degs.Nonempty) :
    (dOfDegrees degs hne = 0 ↔ mOfDegrees degs hne = 0) ∧
      (mOfDegrees degs hne = 0 ↔ ∀ n ∈ degs, n = 0) :=
  ⟨s3135_dOfDegrees_eq_zero_iff degs hne, s3135_mOfDegrees_eq_zero_iff degs hne⟩

/-- Sub-obligations of the remaining Lemma 2.4 steps, with exact corpus lines. -/
def s3135Mzk1Lemma24Remaining : Audit.Obligation :=
  { id := "MZK1.lemma24.remaining-steps"
    source :=
      "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 " ++
        "lines 144-206"
    status := Audit.VerificationStatus.interface
    note :=
      "REMAINING (class B, exactly): (G) Galois-conjugate union closure (lines " ++
        "166-169): replace S by the union of all Gal(Qbar/Q)-conjugates; formal " ++
        "content needed: the conjugate set of an algebraic point is finite and " ++
        "Galois-stable (roots of its minimal polynomial); (F) f0-normalization and " ++
        "coefficient bound |coeffs(f0)| <= d0^d0 (lines 183-199) with the value " ++
        "bounds at S and at the roots S0 of the derivative; (D) descent to the " ++
        "number field F (lines 159-160, Galois-stability + descent of the rational " ++
        "function coefficients); (M) main statement (lines 144-160): exists " ++
        "nonconstant f in Qbar(x) (resp. F(x)) defining phi with (a) phi(S) subset " ++
        "S_phi, (b) phi(beta) outside S_phi, (c) phi unramified over P^1 minus " ++
        "S_phi.  (G) is the next target; (F)/(D)/(M) require the P^1-morphism and " ++
        "descent language.  No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.reduced-degree-induction" ]
    sorryItems :=
      [ "(G) Galois-conjugate union closure (166-169)",
        "(F) f0 coefficient bound (183-199)",
        "(D) descent to F (159-160)",
        "(M) main conclusion (144-160)" ] }

#check s3135_lemma24_induction
#check s3135_lemma24_arithmetic_layer
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24Proof2Actual
end
-- bump-mzk1b-1
-- bump-mzk1b-2