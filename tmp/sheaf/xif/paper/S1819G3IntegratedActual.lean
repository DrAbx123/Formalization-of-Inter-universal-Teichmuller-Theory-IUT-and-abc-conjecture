/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF / S1819

# S1819 -- integrated (G3): the fifth field of PreGaloisCategory is actual

This file integrates the four independent developments

* S1810 S1810.epiSurjective : S1747.EpiSurjective K,
* S1771 S1771FiniteEtaleEpiSplit.exists_prod_algEquiv_of_surjective,
* S1786 S1786.monoInducesIsoOnDirectSummand_of_epiSurjective_of_surjectiveSplit,
* S1793 S1793GaloisAssembly.preGaloisCategory, whose other four fields are actual
  instances from S1745 / S1767 / S1770,

into a PreGaloisCategory (FiniteEtaleAlg K) in which **all five fields are actual
kernel-checked proofs**, with no hypothesis, no sorry, no admit and no new axiom.

The five fields and their sources in the final term are

  field                              source
  ---------------------------------------------------------------------------
  hasTerminal                        S1767 (via S1793.instHasTerminal)
  hasPullbacks                       S1745 (via S1793.instHasPullbacks)
  hasFiniteCoproducts                S1745 (via S1793.instHasFiniteCoproducts)
  hasQuotientsByFiniteGroups         S1770 (via S1793.instHasQuotientsByFiniteGroups)
  monoInducesIsoOnDirectSummand      S1810 + S1771 + S1786 (this file)

## The S1771 -> S1747.SurjectiveSplit bridge (interface differences)

S1771.exists_prod_algEquiv_of_surjective is not stated with the name
S1747.SurjectiveSplit, so the bridge is written explicitly in
S1819.surjectiveSplit.  The differences are purely syntactic:

1. **Universe.**  S1771 states the theorem for {K : Type u} and A B C : Type u.
   S1747 fixes K : Type (universe 0), so the bridge instantiates u = 0.
2. **Direction of the final equality.**  S1771 concludes
   f = (AlgHom.fst K A C).comp e.toAlgHom, while S1747.SurjectiveSplit asks for
   (AlgHom.fst K A C).comp e.toAlgHom = f; the bridge uses he.symm.
3. **Packaging of the existential.**  Both have exactly five components
   (C, CommRing C, Algebra K C, Module.Finite K C, Algebra.Etale K C) followed by
   e : B ≃ₐ[K] A × C; no repackaging is needed.

No mathematical content is changed by the bridge: it is the same product-splitting
statement, only at the universe and with the equality orientation required by S1747.

## Verification (session S1819, 2026-11-01)

* S1771 was compiled to an olean first because no olean existed in the build tree:
  lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1771FiniteEtaleEpiSplitActual.olean
    tmp/sheaf/xif/paper/S1771FiniteEtaleEpiSplitActual.lean
  -> EXIT=0 (two non-fatal linter warnings, no errors).
* This file is compiled with
  lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1819G3IntegratedActual.olean
    tmp/sheaf/xif/paper/S1819G3IntegratedActual.lean
  -> EXIT=0.
* Every #print axioms at the end prints only
  [propext, Classical.choice, Quot.sound]; in particular there is no sorryAx.

## References

* S1810: tmp/sheaf/xif/paper/S1810EpiSurjectiveDedicatedActual.lean
* S1771: tmp/sheaf/xif/paper/S1771FiniteEtaleEpiSplitActual.lean
* S1786: tmp/sheaf/xif/paper/S1786G3CategoricalTransferActual.lean
* S1793: tmp/sheaf/xif/paper/S1793GaloisAssemblyWithQuotientsActual.lean
* Lenstra, *Galois theory for schemes*, Definition 3.1, (G1)--(G3).
-/
import tmp.sheaf.xif.paper.S1810EpiSurjectiveDedicatedActual
import tmp.sheaf.xif.paper.S1771FiniteEtaleEpiSplitActual
import tmp.sheaf.xif.paper.S1786G3CategoricalTransferActual
import tmp.sheaf.xif.paper.S1793GaloisAssemblyWithQuotientsActual

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace S1819

variable {K : Type} [Field K]

/-! ### 1. The two algebraic inputs -/

/-- S1810's theorem, restated with the name used by S1747.  This is definitionally the
same statement; the proof term is S1810's actual proof, not an axiom. -/
theorem epiSurjective : S1747.EpiSurjective K :=
  S1810.epiSurjective (K := K)

/-- S1771's product-splitting theorem is exactly S1747.SurjectiveSplit, after
instantiating S1771's universe u at 0 and reversing the final equality.

This is the only interface work needed to feed S1771 into S1747/S1786; see the
module docstring for the precise list of differences. -/
theorem surjectiveSplit : S1747.SurjectiveSplit K := by
  intro A B _ _ _ _ _ _ _ _ φ hφ
  obtain ⟨C, hCring, hCalg, hCfin, hCet, e, he⟩ :=
    S1771FiniteEtaleEpiSplit.exists_prod_algEquiv_of_surjective (K := K) A B φ hφ
  exact ⟨C, hCring, hCalg, hCfin, hCet, e, he.symm⟩

/-! ### 2. The (G3) field, actual -/

/-- **The (G3) field for (CommAlgCat.FiniteEtale K)^op is actual.**

This is exactly the type S1786.MonoInducesIsoOnDirectSummandField K, proved from
S1810 (EpiSurjective) and the S1771 -> S1747.SurjectiveSplit bridge via S1786's
categorical transfer.  No hypothesis remains. -/
theorem monoInducesIsoOnDirectSummandField :
    S1786.MonoInducesIsoOnDirectSummandField K :=
  S1786.monoInducesIsoOnDirectSummand_of_epiSurjective_of_surjectiveSplit
    (K := K) (epiSurjective (K := K)) (surjectiveSplit (K := K))

/-- The same actual (G3) field in the shape used by S1793.

S1793.MonoInducesIsoOnDirectSummandField is S1767's abbreviation, whose body is
literally the same Pi type as S1786.MonoInducesIsoOnDirectSummandField; the two
categories are both (CommAlgCat.FiniteEtale.{0} K)^op.  The proof is therefore the
same term, checked by definitional unfolding. -/
theorem monoInducesIsoOnDirectSummandField_S1793 :
    S1793GaloisAssembly.MonoInducesIsoOnDirectSummandField K :=
  monoInducesIsoOnDirectSummandField (K := K)

/-! ### 3. The pre-Galois category with all five fields actual -/

/-- **Main theorem of S1819.**  (CommAlgCat.FiniteEtale K)^op is a pre-Galois
category, with all five fields actual:

* hasTerminal, hasPullbacks, hasFiniteCoproducts, hasQuotientsByFiniteGroups are
  S1793's actual instances (from S1767, S1745, S1745, S1770 respectively);
* monoInducesIsoOnDirectSummand is monoInducesIsoOnDirectSummandField_S1793 above
  (from S1810 + S1771 + S1786).

There is no hypothesis in the statement. -/
theorem preGaloisCategory :
    PreGaloisCategory (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  S1793GaloisAssembly.preGaloisCategory (K := K)
    (monoInducesIsoOnDirectSummandField_S1793 (K := K))

/-- The constructed term has the five expected field types.  These are type checks,
not additional assumptions. -/
example : HasTerminal (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  (preGaloisCategory (K := K)).hasTerminal

example : HasPullbacks (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  (preGaloisCategory (K := K)).hasPullbacks

example : HasFiniteCoproducts (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  (preGaloisCategory (K := K)).hasFiniteCoproducts

example : ∀ (G : Type) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  (preGaloisCategory (K := K)).hasQuotientsByFiniteGroups

example : ∀ {X Y : S1793GaloisAssembly.FiniteEtaleAlg K} (i : X ⟶ Y) [Mono i],
    ∃ (Z : S1793GaloisAssembly.FiniteEtaleAlg K) (u : Z ⟶ Y),
      Nonempty (IsColimit (BinaryCofan.mk i u)) :=
  (preGaloisCategory (K := K)).monoInducesIsoOnDirectSummand

end S1819

/-! ### Axiom audit -/

#print axioms S1819.epiSurjective
#print axioms S1819.surjectiveSplit
#print axioms S1819.monoInducesIsoOnDirectSummandField
#print axioms S1819.monoInducesIsoOnDirectSummandField_S1793
#print axioms S1819.preGaloisCategory
