/-
  Reduction pass C2b: the Frobenius-picture oriented graph Gamma and its graph
  automorphisms (Corollary 3.8 of IUT I).

  Paper anchors (`D:\lean\papers\motizuki_corpus\text\Inter-universal
  Teichmuller Theory I.txt`):

  * Corollary 3.8, lines 5039--5064: for a collection `{nHT^Theta}_{n in Z}`
    of distinct Theta-Hodge theaters, consecutive members are Theta-linked,
    yielding an infinite chain; "This infinite chain may be represented
    symbolically as an oriented graph Gamma [cf. [AbsTopIII], Sec. 0]"
    (line 5052), displayed as `... -> bullet -> bullet -> bullet -> ...`,
    "i.e., where the arrows correspond to the Theta->'s, and the bullet's
    correspond to the nHT^Theta" (lines 5054--5057).  "This oriented graph
    Gamma carries a natural action by Z -- i.e., a translation symmetry --
    but no arbitrary permutation symmetries.  For instance, Gamma has no
    automorphism that switches two adjacent vertices, but leaves the
    remaining vertices fixed" (lines 5057--5060);
    the chain structure is "Frobenius-like", or "order-conscious"
    (lines 5061--5063).

  Frozen obligation addressed by this file (new in this pass):
  `IUT-I.theta-link-graph-automorphism-reduction`.  It continues
  `IUT-I.theta-link-displacement-reduction` (companion file
  `SourceThetaLinkDisplacementReduction.lean`), whose reduction list marked
  the ordered graph Gamma and its graph-automorphism Z-action as a gap.

  Proved in this file:

  1. The oriented graph Gamma as the adjacency relation `m = n + 1` on the
     vertex set Z, and its graph automorphisms (permutations of the vertex
     set preserving the arrow relation, in both directions).
  2. First classification: a permutation is a graph automorphism of Gamma
     precisely when it preserves the successor operation.
  3. The Z-action: every translation `n |-> n + k` is a graph automorphism;
     conversely every graph automorphism is a translation; the graph
     automorphisms are closed under identity, composition and inverse.
  4. Corollary 3.8's explicit example at graph level: no graph automorphism
     switches two adjacent vertices while fixing the remaining vertices; in
     particular the adjacent transposition is not a graph automorphism,
     although it does fix all remaining vertices.
  5. Freeness on a labeled picture: for a `SourceThetaLinkChain`, a graph
     automorphism acts on the labeling by an index shift `n |-> n + k`, and
     the only translation preserving the labeling is the identity shift.

  Reductions (explicitly marked; none of these is the original statement):

  * The graph is formalized on the vertex set Z of indices; the labeling by
    Theta-Hodge theaters is carried by `SourceThetaLinkChain` (injective
    `theater` field), and item 5 connects the two levels.  The graph of a
    specific collection `{nHT^Theta}` is not constructed here (card C1,
    unchanged).
  * The "action by Z" is the statement that the translations are exactly the
    graph automorphisms, with the group laws inherited from the companion
    file's `chainTranslation` (apply/zero/composition/inverse).  The
    Frobenius-like / order-conscious discussion of [FrdI], Sec. I4
    (lines 5061--5063) is represented by "graph automorphism =
    successor-preserving" plus the no-adjacent-switch theorem.
  * The scheme-theoretic realization of the displacement between the q-side
    and the Theta-side (Fig. 3.1) remains card C2b of the companion file.
-/

import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkDisplacementReduction
import Init.Omega

set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon

/-! ## 1. The oriented graph Gamma of the Frobenius picture -/

/-- The arrows of the Frobenius-picture graph `Gamma` (Corollary 3.8, line
5052): the vertices are the integer indices, with one arrow `n --> n + 1`
for each `n`. -/
def FrobeniusPictureArrow (n m : Int) : Prop :=
  m = n + 1

/-- An automorphism of the oriented graph `Gamma`: a permutation of the
vertex set preserving the arrow relation, in both directions. -/
def FrobeniusPictureGraphAut (σ : Equiv.Perm Int) : Prop :=
  ∀ n m : Int, FrobeniusPictureArrow n m ↔ FrobeniusPictureArrow (σ n) (σ m)

/-! ## 2. Graph automorphisms are exactly the successor-preserving maps -/

theorem graphAut_step {σ : Equiv.Perm Int} (hσ : FrobeniusPictureGraphAut σ)
    (n : Int) : σ (n + 1) = σ n + 1 :=
  (hσ n (n + 1)).mp rfl

theorem step_graphAut (σ : Equiv.Perm Int)
    (hσ : ∀ n : Int, σ (n + 1) = σ n + 1) : FrobeniusPictureGraphAut σ := by
  intro n m
  constructor
  · intro h
    have hm : m = n + 1 := h
    change σ m = σ n + 1
    rw [hm, hσ n]
  · intro h
    have hm : σ m = σ n + 1 := h
    change m = n + 1
    exact σ.injective (hm.trans (hσ n).symm)

theorem graphAut_iff_stepPreserving (σ : Equiv.Perm Int) :
    FrobeniusPictureGraphAut σ ↔ ∀ n : Int, σ (n + 1) = σ n + 1 :=
  ⟨graphAut_step, step_graphAut σ⟩

/-! ## 3. The Z-action: graph automorphisms are exactly the translations -/

theorem chainTranslation_graphAut (k : Int) :
    FrobeniusPictureGraphAut (chainTranslation k) :=
  step_graphAut _ (chainTranslation_stepPreserving k)

theorem chainTranslation_injective : Function.Injective chainTranslation := by
  intro k l h
  have h0 := congrArg (fun e : Equiv.Perm Int => e 0) h
  simp [chainTranslation_apply] at h0
  omega

theorem graphAut_translation (σ : Equiv.Perm Int) (hσ : FrobeniusPictureGraphAut σ) :
    ∃ k : Int, ∀ n : Int, σ n = n + k :=
  chainStepPreserving_eq_translation σ ((graphAut_iff_stepPreserving σ).mp hσ)

theorem graphAut_eq_translation (σ : Equiv.Perm Int) :
    FrobeniusPictureGraphAut σ ↔ ∃ k : Int, σ = chainTranslation k := by
  constructor
  · intro hσ
    obtain ⟨k, hk⟩ := graphAut_translation σ hσ
    refine ⟨k, Equiv.ext (fun n => ?_)⟩
    rw [chainTranslation_apply]
    exact hk n
  · rintro ⟨k, hk⟩
    rw [hk]
    exact chainTranslation_graphAut k

theorem graphAut_one : FrobeniusPictureGraphAut 1 :=
  step_graphAut 1 (fun n => by simp)

theorem graphAut_comp {σ τ : Equiv.Perm Int}
    (hσ : FrobeniusPictureGraphAut σ) (hτ : FrobeniusPictureGraphAut τ) :
    FrobeniusPictureGraphAut (τ.trans σ) := by
  apply step_graphAut
  intro n
  have hσ' := (graphAut_iff_stepPreserving σ).mp hσ
  have hτ' := (graphAut_iff_stepPreserving τ).mp hτ
  simp only [Equiv.trans_apply]
  rw [hτ' n, hσ' (τ n)]

theorem graphAut_symm {σ : Equiv.Perm Int} (hσ : FrobeniusPictureGraphAut σ) :
    FrobeniusPictureGraphAut σ.symm := by
  intro n m
  have h := hσ (σ.symm n) (σ.symm m)
  simpa only [Equiv.apply_symm_apply] using h.symm

/-! ## 4. No automorphism switches two adjacent vertices -/

theorem adjacentSwap_fixes_other_vertices (n m : Int) (hmn : m ≠ n)
    (hmn' : m ≠ n + 1) : Equiv.swap n (n + 1) m = m :=
  Equiv.swap_apply_of_ne_of_ne hmn hmn'

theorem adjacentSwap_switches_and_fixes (n : Int) :
    Equiv.swap n (n + 1) n = n + 1 ∧ Equiv.swap n (n + 1) (n + 1) = n ∧
      (∀ m : Int, m ≠ n → m ≠ n + 1 → Equiv.swap n (n + 1) m = m) :=
  ⟨Equiv.swap_apply_left n (n + 1), Equiv.swap_apply_right n (n + 1),
    adjacentSwap_fixes_other_vertices n⟩

theorem no_automorphism_switches_adjacent_vertices (n : Int) :
    ¬ ∃ σ : Equiv.Perm Int, FrobeniusPictureGraphAut σ ∧ σ n = n + 1 ∧
      σ (n + 1) = n ∧ (∀ m : Int, m ≠ n → m ≠ n + 1 → σ m = m) := by
  rintro ⟨σ, hσ, hforward, hback, -⟩
  obtain ⟨k, hk⟩ := graphAut_translation σ hσ
  have hk1 : k = 1 := by
    have h := hk n
    rw [hforward] at h
    omega
  have h2 := hk (n + 1)
  rw [hback, hk1] at h2
  omega

theorem adjacentSwap_not_graphAut (n : Int) :
    ¬ FrobeniusPictureGraphAut (Equiv.swap n (n + 1)) := by
  intro h
  have hs := (graphAut_iff_stepPreserving (Equiv.swap n (n + 1))).mp h n
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at hs
  omega

/-! ## 5. Freeness of the Z-action on a labeled picture -/

namespace SourceThetaLinkChain

variable {l : PrimeGeFive} {V : Type uv}

/-- A graph automorphism of Gamma acts on the labeling of a Frobenius-picture
chain by an index shift: the theater at a permuted position is a shift of the
original labeling. -/
theorem graphAut_index_translation (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V)
    {σ : Equiv.Perm Int} (hσ : FrobeniusPictureGraphAut σ) :
    ∃ k : Int, ∀ n : Int, C.theater (σ n) = C.theater (n + k) := by
  obtain ⟨k, hk⟩ := graphAut_translation σ hσ
  exact ⟨k, fun n => by rw [hk n]⟩

/-- The only translation that preserves the labeling of a Frobenius-picture
chain is the identity shift: the Z-action on the picture is free. -/
theorem labelPreservingTranslation_iff (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V)
    (k : Int) : (∀ n : Int, C.theater (n + k) = C.theater n) ↔ k = 0 := by
  constructor
  · intro h
    have hk : (0 : Int) + k = 0 := C.distinct (h 0)
    omega
  · intro hk
    subst hk
    intro n
    simp

end SourceThetaLinkChain

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def thetaLinkGraphAutomorphismReduction : Obligation :=
  { id := "IUT-I.theta-link-graph-automorphism-reduction"
    source :=
      "IUT I: Corollary 3.8 (the oriented graph Gamma of the Frobenius " ++
        "picture: natural action by Z -- a translation symmetry -- and no " ++
        "automorphism switching two adjacent vertices while fixing the rest)"
    status := VerificationStatus.interface
    note :=
      "Reduction pass C2b for the oriented graph Gamma of Corollary 3.8. " ++
        "Proved here: (1) the adjacency relation m = n + 1 of Gamma on the " ++
        "vertex set Z and its graph automorphisms; (2) graph automorphisms " ++
        "are exactly the successor-preserving permutations; (3) the " ++
        "Z-translations are exactly the graph automorphisms, closed under " ++
        "identity, composition and inverse; (4) no graph automorphism " ++
        "switches two adjacent vertices while fixing the remaining vertices " ++
        "(the adjacent transposition is not a graph automorphism, although " ++
        "it does fix the remaining vertices); (5) on a SourceThetaLinkChain " ++
        "a graph automorphism acts on the labeling by an index shift, and " ++
        "the only labeling-preserving translation is the identity shift. " ++
        "Reductions: the graph is formalized on the index set Z and the " ++
        "labeling by Theta-Hodge theaters is carried by " ++
        "SourceThetaLinkChain; the graph of a specific collection " ++
        "{nHT^Theta} is not constructed (card C1), and the scheme-theoretic " ++
        "realization of Fig. 3.1 remains card C2b."
    dependsOn :=
      [ "IUT-I.theta-link-displacement-reduction",
        "IUT-I.hodge-theater-family-source-laws",
        "IUT-I.hodge-theater-histories" ] }

end LeanFormal.IUT.Audit
