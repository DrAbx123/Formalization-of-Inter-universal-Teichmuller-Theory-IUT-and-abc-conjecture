import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3132CompletionComparisonToolActual

universe u

/-!
# task-65: generic completion-comparison tool (manufactured asset)

**Component, not a paper object.**  Owner: hull.  Consumers: the fiber half of
the uniform HDD/C3 comparison (`MissingOneColumnC3FiberComparisonData` in
`S3132UniformFiberMissingActual`); mainline registry; shehdd gate.

Generic tool, fully proved:

* `algEquiv_self_of_finrank_one`: a field `E` finite-dimensional over a field
  `k` with `finrank_k E = 1` is `k`-algebra-isomorphic to `k`.  (The algebra
  map is injective because `k` is a field and `E` is nontrivial, and it is
  surjective by rank-nullity; then `AlgEquiv.ofBijective`.)
* `ringEquiv_of_two_finrank_one`: two such fields over the *same* base `k` are
  ring-isomorphic.
* `completionAlgEquivPadic_of_finrank_one` / `completionRingEquivPadic`: a
  completion of a number field at a finite place is isomorphic to its p-adic
  scalar field `PadicScalarField place` when the local degree is one.

The INSTANTIATION data (the actual local degree-one comparison of the C3 packet
fibers with the rational one-column completions, and the place/prime matching) is
NOT part of the tool: it is a named exact missing
(`S3132FiberCorrectedMissingActual`); this separation keeps the tool a permanent
reusable asset and makes the fiber missing pure data instantiation.
Pages: IUT III, Proposition 3.2, (ii), pp. 97-99; Proposition 3.7, (ii), (v),
pp. 108-112.
-/

/-- **Generic tool:** a field finite-dimensional of `k`-rank one over a field `k`
is `k`-algebra-isomorphic to `k`. -/
theorem algEquiv_self_of_finrank_one
    {k E : Type*} [Field k] [Field E] [Algebra k E] [Module.Finite k E]
    (h : Module.finrank k E = 1) : E ≃ₐ[k] k := by
  have hinj : Function.Injective (algebraMap k E) := by
    have hker : RingHom.ker (algebraMap k E) = ⊥ := by
      rcases Ideal.eq_bot_or_top (RingHom.ker (algebraMap k E)) with hb | ht
      · exact hb
      · exfalso
        have hmem : (1 : k) ∈ RingHom.ker (algebraMap k E) := by
          rw [ht]; trivial
        simpa [RingHom.mem_ker] using hmem
    exact (RingHom.ker_eq_bot_iff _).mp hker
  have hsurj : Function.Surjective (algebraMap k E) := by
    have hker0 : LinearMap.ker (Algebra.linearMap k E) = ⊥ :=
      LinearMap.ker_eq_bot.mpr hinj
    have hd := LinearMap.finrank_range_add_finrank_ker (Algebra.linearMap k E)
    rw [hker0, finrank_bot, add_zero] at hd
    have htop : LinearMap.range (Algebra.linearMap k E) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have htopfr : Module.finrank k (⊤ : Submodule k E) = 1 := by
        rw [Submodule.finrank_top, h]
      rw [hd, htopfr]
    exact (LinearMap.range_eq_top).mp htop
  exact (AlgEquiv.ofBijective (Algebra.ofId k E) ⟨hinj, hsurj⟩).symm

/-- **Generic tool (two fields, same base):** two finite-dimensional `k`-fields of
`k`-rank one are ring-isomorphic. -/
theorem ringEquiv_of_two_finrank_one
    {k E1 E2 : Type*} [Field k] [Field E1] [Algebra k E1] [Module.Finite k E1]
    [Field E2] [Algebra k E2] [Module.Finite k E2]
    (h1 : Module.finrank k E1 = 1) (h2 : Module.finrank k E2 = 1) :
    Nonempty (E1 ≃+* E2) :=
  ⟨(algEquiv_self_of_finrank_one h1).toRingEquiv.trans
    (algEquiv_self_of_finrank_one h2).symm.toRingEquiv⟩

/-- **Completion instance of the tool:** a completion at a finite place whose
local degree over its p-adic scalar field is one is isomorphic to that scalar
field. -/
theorem completionAlgEquivPadic_of_finrank_one
    {K : Type*} [Field K] [NumberField K] (place : NumberField.FinitePlace K)
    (h : Module.finrank (PadicScalarField place) (Completion place) = 1) :
    Completion place ≃ₐ[PadicScalarField place] PadicScalarField place :=
  algEquiv_self_of_finrank_one h

/-- **Completion instance (ring form).** -/
theorem completionRingEquivPadic_of_finrank_one
    {K : Type*} [Field K] [NumberField K] (place : NumberField.FinitePlace K)
    (h : Module.finrank (PadicScalarField place) (Completion place) = 1) :
    Nonempty (Completion place ≃+* PadicScalarField place) :=
  ⟨(completionAlgEquivPadic_of_finrank_one place h).toRingEquiv⟩

#check algEquiv_self_of_finrank_one
#check ringEquiv_of_two_finrank_one
#check completionAlgEquivPadic_of_finrank_one
#check completionRingEquivPadic_of_finrank_one

end LeanFormal.IUT.XiFPaper.S3132CompletionComparisonToolActual

end
