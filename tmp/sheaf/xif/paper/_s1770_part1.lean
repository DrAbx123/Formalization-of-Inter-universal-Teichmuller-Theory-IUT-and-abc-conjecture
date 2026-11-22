/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF / S1770
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.TotallySplit
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Galois.Basic

/-!
# S1770: fixed points of finite etale K-algebras and (G2) for (FiniteEtale K)^op

For a field K, a finite etale K-algebra A and a finite group G acting on A
by K-algebra automorphisms, this file

1. constructs the invariant subalgebra A^G = fixedSubalgebra of A;
2. proves that A^G is finite etale over K again (Galois descent along K -> Kbar,
   reduced to the separably closed case Kbar^n, where a subalgebra of Kbar^n is
   Kbar^m);
3. proves the universal property of A^G: in the category CommAlgCat.FiniteEtale K,
   the cone with point A^G and structural maps the inclusions A^G -> A is a limit
   cone for the action diagram (so in the opposite category (FiniteEtale K)^op,
   which is the Galois category of finite etale K-schemes, A^G is the colimit,
   i.e. the categorical quotient, with quotient map A -> A^G);
4. fills the field hasQuotientsByFiniteGroups of
   PreGaloisCategory ((CommAlgCat.FiniteEtale K)^op).

Mathlib contains neither the invariant subalgebra construction for finite etale
algebras nor the Galois descent statement that a subalgebra of a finite etale algebra is
finite etale; both are supplied here (Section 1 and Section 2).

No proof in this file is left unfinished.  The only axioms are the three standard ones
(propext, Classical.choice, Quot.sound), audited at the end of the file.

## Main results

* S1770.etale_subalgebra: a K-subalgebra of a finite etale K-algebra is etale
  (hence, being a submodule of a finite module over a field, finite etale).
* S1770.invariants: the invariant subalgebra A^G.
* S1770.invariantsCone, S1770.invariantsIsLimit: the limit cone over a
  G-action with point A^G.
* S1770.hasQuotientsByFiniteGroups: HasColimitsOfShape (SingleObj G)
  in (CommAlgCat.FiniteEtale K)^op for every finite group G.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1770

universe u v w

/-! ## 1. Subalgebras of finite etale algebras are finite etale

The mathematical content is Galois descent along the faithfully flat extension
K -> Kbar: over a separably closed field, a subalgebra of Kbar^n is Kbar^m.
The auxiliary statement finiteSplit_of_injective_pi is that reduction. -/

section EtaleSubalgebra

variable {K : Type u} [Field K]

/-- If a K-algebra R embeds into a finite power of a separably closed field K,
then R is K-split. -/
theorem finiteSplit_of_injective_pi {R : Type v} [CommRing R] [Algebra K R]
    {ι : Type w} [Finite ι] (f : R →ₐ[K] (ι → K)) (hf : Function.Injective f) :
    Algebra.IsFiniteSplit K R := by
  classical
  by_cases hR : Subsingleton R
  · exact Algebra.IsFiniteSplit.of_subsingleton_top
  haveI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
  have hι : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    haveI : IsEmpty ι := h
    exact hR (hf.subsingleton)
  let p (i : ι) : R →ₐ[K] K := (Pi.evalAlgHom K (fun _ : ι => K) i).comp f
  have hp_surj (i : ι) : Function.Surjective (p i) := by
    intro x
    refine ⟨algebraMap K R x, ?_⟩
    simp [p]
  have hp_max (i : ι) : (RingHom.ker (p i)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (p i) (hp_surj i)
  let σ : Type v := ↥(Set.range fun i : ι => RingHom.ker (p i))
  haveI : Fintype σ := Fintype.ofFinite σ
  let rep (I : σ) : ι := Classical.choose I.property
  have rep_spec (I : σ) : RingHom.ker (p (rep I)) = (I : Ideal R) :=
    Classical.choose_spec I.property
  have hmax (I : σ) : (I : Ideal R).IsMaximal := by
    rw [← rep_spec I]
    exact hp_max (rep I)
  have hcoprime : Pairwise (Function.onFun IsCoprime (fun I : σ => (I : Ideal R))) := by
    intro I J hIJ
    haveI := hmax I
    haveI := hmax J
    exact Ideal.isCoprime_of_isMaximal (by intro h; exact hIJ (Subtype.ext h))
  have hinf : (⨅ I : σ, (I : Ideal R)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    apply hf
    ext i
    have hx' : x ∈ (⨅ I : σ, (I : Ideal R)) := hx
    have hxker : x ∈ RingHom.ker (p i) :=
      (Submodule.mem_iInf _).mp hx' ⟨RingHom.ker (p i), ⟨i, rfl⟩⟩
    simpa [p] using hxker
  let fI : σ → Ideal R := fun I => (I : Ideal R)
  let Iinf : Ideal R := ⨅ I : σ, fI I
  let e_crt_ring : R ⧸ Iinf ≃+* ((I : σ) → R ⧸ fI I) :=
    Ideal.quotientInfRingEquivPiQuotient fI hcoprime
  let e_crt := AlgEquiv.ofRingEquiv (R := K) (f := e_crt_ring) (by
    intro x
    ext I
    trans Ideal.Quotient.mk (fI I) (algebraMap K R x)
    · rw [← Ideal.Quotient.mk_algebraMap]
      exact congrFun (Ideal.quotientInfToPiQuotient_mk fI (algebraMap K R x)) I
    · rfl)
  let qe (I : σ) := (Ideal.quotientEquivAlgOfEq K (rep_spec I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := p (rep I)) (hp_surj (rep I)))
  let e3 := AlgEquiv.piCongrRight (fun I : σ => qe I)
  let e1 := (AlgEquiv.quotientBot K R).symm.trans (Ideal.quotientEquivAlgOfEq K hinf).symm
  let e := e1.trans (e_crt.trans e3)
  exact ⟨Fintype.card σ, ⟨e.trans (AlgEquiv.piCongrLeft' K (fun _ : σ => K) (Fintype.equivFin σ))⟩⟩