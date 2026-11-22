/-
  Reduction pass: distinct histories and their links (obligation
  `IUT-I.hodge-theater-histories`: "Construct distinct histories and their
  links; do not use an unconstrained record.").

  Paper anchors (`D:\lean\papers\motizuki_corpus\text\Inter-universal
  Teichmuller Theory I.txt`):

  * Corollary 3.7 (i), lines 4963--4981: for Theta-Hodge theaters
    dagger-HT, ddagger-HT relative to fixed initial Theta-data, the full
    poly-isomorphism dagger-F_tht ~> ddagger-F_mod is nonempty; it is
    called the Theta-link.
  * Corollary 3.8, lines 5039--5064: "Let {nHT^Theta}_{n in Z} be a
    collection of distinct Theta-Hodge theaters indexed by the integers.
    Then by applying Corollary 3.7, (i), ... we obtain an infinite chain
    ... of Theta-linked Theta-Hodge theaters"; the chain "carries a natural
    action by Z -- i.e., a translation symmetry -- but it has no
    arbitrary permutation symmetries"; it "has no automorphism that
    switches two adjacent vertices, but leaves the remaining vertices
    fixed"; the structure is "Frobenius-like", or "order-conscious".
  * Summary, lines 622--642: a collection of distinct Theta-pm-ell-NF
    Hodge theaters yields "an infinite chain ... of Theta-linked
    Theta-pm-ell-NF-Hodge theaters ... the Frobenius-picture", which
    "has no permutation automorphisms that switch adjacent indices
    n, n+1, but leave the remaining indices in Z fixed".

  Source-location refinement (recorded, not a change of statement): the
  obligation cites IUT I, Sections 4--5, which construct the theaters
  whose distinctness the chain presupposes; the chain-of-links statements
  formalized here are Corollaries 3.7--3.8 (Section 3) and the Section I1
  summary.

  Frozen proposition carried by this file (reduction; not the original
  statement): for a Z-indexed chain of distinct theaters with consecutive
  Theta-links (a `SourceThetaLinkChain` of the C2 pass) and any start `a`
  and length `k`, the window [a, a+k] is a history in the dependent-chain
  sense (`HodgeTheaterHistory`, History.lean):

  * terminal law `terminal = theater (a+k)`, length law `length = k+1`,
    and q/scale transport along the window through the composite link;
  * separation: positions with distinct indices carry distinct theaters;
  * distinct histories: different window lengths at the same start give
    different histories, and different terminals give different histories;
  * rigidity: the only index permutation preserving every window terminal
    is the identity; the adjacent transposition and the unit shift fail
    (the history-level form of Corollary 3.8's exclusion).

  Not proved (cards): the existence of the chain {nHT} from arbitrary
  initial Theta-data (card C1, unchanged); the anabelian/scheme-theoretic
  interpretation of the links (the carrier collapses the two sides; cards
  C2/C2b).  The window construction presupposes a supplied chain and is
  not a construction of the chain itself.

  Consumers: `IUT-I.hodge-theater-histories`
  (`IUTI\InitialTheta\SourceObligations.lean:66`), SourceHodgeTheaterBridge
  (D3.1 `IUTIII\Theorem311\SourceOriginalInput.lean:41-46`), and the
  Theorem 3.11 source chain
  (`IUTIII\Theorem311\SourceH1H2Construction.lean:272-277`).
-/

import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkGraphAutomorphismReduction
import LeanFormal.IUT.IUTI.HodgeTheater.History
import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamilyLawsReduction
import Init.Omega

set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. Window histories of a Frobenius-picture chain -/

namespace SourceThetaLinkChain

/-- The window history of the chain starting at position `a`: the dependent
chain of the `k` consecutive Theta-links from `a` to `a + k`. -/
def windowHistory (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V)
    (a : Int) : (k : Nat) → HodgeTheaterHistory l V (C.theater a)
  | 0 => HodgeTheaterHistory.singleton (C.theater a)
  | k + 1 =>
      HodgeTheaterHistory.cons (C.step a) (windowHistory C (a + 1) k)

@[simp] theorem windowHistory_zero
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (a : Int) :
    C.windowHistory a 0 = HodgeTheaterHistory.singleton (C.theater a) := rfl

@[simp] theorem windowHistory_succ
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (a : Int) (k : Nat) :
    C.windowHistory a (k + 1) =
      HodgeTheaterHistory.cons (C.step a) (C.windowHistory (a + 1) k) := rfl

@[simp] theorem windowHistory_terminal_succ
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (a : Int) (k : Nat) :
    (C.windowHistory a (k + 1)).terminal =
      (C.windowHistory (a + 1) k).terminal := rfl

theorem windowHistory_terminal
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (a : Int) (k : Nat) :
    (C.windowHistory a k).terminal = C.theater (a + (k : Int)) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
      rw [windowHistory_terminal_succ, ih (a + 1)]
      congr 1
      omega

theorem windowHistory_length
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (a : Int) (k : Nat) :
    (C.windowHistory a k).length = k + 1 := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
      rw [windowHistory_succ, HodgeTheaterHistory.length_cons, ih (a + 1)]

theorem windowHistory_thetaQ
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (a : Int) (k : Nat) :
    (C.theater a).thetaPacket.q = (C.theater (a + (k : Int))).thetaPacket.q := by
  have h := (C.windowHistory a k).composite_q
  rw [windowHistory_terminal] at h
  exact h

theorem windowHistory_thetaScale
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (a : Int) (k : Nat)
    (j : SignedLabel l.value) :
    (C.theater a).thetaPacket.scale j =
      (C.theater (a + (k : Int))).thetaPacket.scale j := by
  have h := (C.windowHistory a k).composite_scale j
  rw [windowHistory_terminal] at h
  exact h

/-! ## 2. Separation and distinctness of window histories -/

theorem windowHistory_position_ne
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (a : Int) {i j : Nat}
    (hij : i ≠ j) :
    C.theater (a + (i : Int)) ≠ C.theater (a + (j : Int)) := by
  intro h
  have h' : (i : Int) = (j : Int) := by
    have := C.distinct h
    omega
  exact hij (Int.ofNat_inj.mp h')

theorem windowHistory_terminal_ne_shift
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (a : Int) (k : Nat) :
    (C.windowHistory a k).terminal ≠ (C.windowHistory (a + 1) k).terminal := by
  rw [windowHistory_terminal, windowHistory_terminal]
  intro h
  have := C.distinct h
  omega

theorem windowHistory_succ_ne
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (a : Int) (k : Nat) :
    C.windowHistory a (k + 1) ≠ C.windowHistory a k := by
  intro h
  have hl := congrArg HodgeTheaterHistory.length h
  rw [windowHistory_length, windowHistory_length] at hl
  omega

theorem windowHistory_ne_of_terminal_ne
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (a : Int) {k k' : Nat}
    (h : C.theater (a + (k : Int)) ≠ C.theater (a + (k' : Int))) :
    C.windowHistory a k ≠ C.windowHistory a k' := by
  intro hh
  apply h
  have ht : (C.windowHistory a k).terminal =
      (C.windowHistory a k').terminal := congrArg HodgeTheaterHistory.terminal hh
  rwa [windowHistory_terminal, windowHistory_terminal] at ht

theorem windowHistory_terminal_rigidity
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (sigma : Equiv.Perm Int)
    (h_sigma : ∀ a k, (C.windowHistory (sigma a) k).terminal =
      (C.windowHistory a k).terminal) :
    sigma = 1 := by
  apply C.index_automorphism_eq_one sigma
  intro a
  have h := h_sigma a 0
  simpa using h

theorem windowHistory_adjacent_swap_not_preserving
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) :
    ¬ (∀ a k, (C.windowHistory (Equiv.swap 0 1 a) k).terminal =
      (C.windowHistory a k).terminal) := by
  intro h
  apply C.adjacent_swap_not_preserving
  intro n
  have h' := h n 0
  simpa using h'

theorem windowHistory_shift_not_preserving
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) :
    ¬ (∀ a k, (C.windowHistory (a + 1) k).terminal =
      (C.windowHistory a k).terminal) := by
  intro h
  apply C.shift_not_preserving
  intro n
  have h' := h n 0
  simpa using h'

end SourceThetaLinkChain

/-! ## 3. Concrete witnesses -/

namespace FiniteIntegralTwoTheaterHistory

/-- The one-step history `false -> true` of the concrete two-member family:
an actual link between two distinct finite-integral theaters. -/
def twoTheaterStepHistory (l : PrimeGeFive) :
    HodgeTheaterHistory l (FinitePrimePlace 2 7)
      ((finiteIntegralTwoTheaterFamily l).theater false) :=
  HodgeTheaterHistory.cons
    ((finiteIntegralTwoTheaterFamily l).link false true)
    (HodgeTheaterHistory.singleton
      ((finiteIntegralTwoTheaterFamily l).theater true))

@[simp] theorem twoTheaterStepHistory_terminal (l : PrimeGeFive) :
    (twoTheaterStepHistory l).terminal =
      (finiteIntegralTwoTheaterFamily l).theater true := rfl

@[simp] theorem twoTheaterStepHistory_length (l : PrimeGeFive) :
    (twoTheaterStepHistory l).length = 2 := rfl

theorem twoTheaterStepHistory_thetaQ (l : PrimeGeFive) :
    ((finiteIntegralTwoTheaterFamily l).theater false).thetaPacket.q =
      ((finiteIntegralTwoTheaterFamily l).theater true).thetaPacket.q :=
  (twoTheaterStepHistory l).composite_q

theorem twoTheaterStepHistory_composite_eq_link (l : PrimeGeFive) :
    (twoTheaterStepHistory l).composite =
      (finiteIntegralTwoTheaterFamily l).link false true := by
  simp [twoTheaterStepHistory, HodgeTheaterLink.trans_refl]

theorem twoTheaterStepHistory_source_ne_terminal (l : PrimeGeFive) :
    (finiteIntegralTwoTheaterFamily l).theater false ≠
      (twoTheaterStepHistory l).terminal := by
  rw [twoTheaterStepHistory_terminal]
  exact finiteIntegralTwoTheaterFamily_theater_ne l

end FiniteIntegralTwoTheaterHistory

/-! ## 4. Degenerate witnesses (precise negatives) -/

/-- A constant family over `Bool` is never injective: the paper's
distinctness precondition is non-vacuous (the reflexive concrete history of
History.lean is the degenerate case). -/
theorem constantTheaterFamily_not_injective {l : PrimeGeFive} {V : Type uv}
    (T : HodgeTheater.{ua, uv, upi, umon} l V) :
    ¬ Function.Injective (fun _ : Bool => T) := by
  intro h
  exact Bool.false_ne_true (h rfl)

/-- The reflexive three-step concrete history has the reflexive link as its
composite: it is a genuine history, but not a distinct-history witness. -/
theorem gaussianFiniteIntegralHistory_composite_refl (l : PrimeGeFive) :
    (gaussianFiniteIntegralHistory l).composite =
      HodgeTheaterLink.refl (gaussianFiniteIntegralHodgeTheater l) := by
  simp [gaussianFiniteIntegralHistory, HodgeTheaterLink.trans_refl]

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def hodgeTheaterHistoriesReduction : Obligation :=
  { id := "IUT-I.hodge-theater-histories-reduction"
    source :=
      "IUT I: Corollary 3.7 (i) (the Theta-link between Theta-Hodge " ++
        "theaters) and Corollary 3.8 (Frobenius-pictures: distinct " ++
        "theaters indexed by Z, the chain of Theta-links, Z-translation " ++
        "symmetry, no adjacent-switch automorphism); Summary, lines " ++
        "622--642 (the Frobenius-picture of Theta-pm-ell-NF-Hodge theaters)"
    status := VerificationStatus.interface
    note :=
      "Reduction pass for `IUT-I.hodge-theater-histories`: the window " ++
        "histories of a Z-indexed chain of distinct theaters with " ++
        "consecutive Theta-links are constructed as dependent chains in " ++
        "the sense of `HodgeTheaterHistory` (History.lean), with terminal " ++
        "law, length law, q/scale transport, position separation, distinct " ++
        "histories (by length and by terminal), and the history-level " ++
        "rigidity: only the identity index permutation preserves all " ++
        "window terminals, while the adjacent transposition and the unit " ++
        "shift fail. A concrete Bool-indexed witness (false -> true with " ++
        "distinct endpoints and one real link) and the degenerate reflexive " ++
        "history (composite = refl) are recorded. Not proved: the existence " ++
        "of the chain {nHT} from arbitrary initial Theta-data (card C1); " ++
        "the anabelian/scheme-theoretic interpretation of the links (cards " ++
        "C2/C2b); the window construction presupposes a supplied chain and " ++
        "is not a construction of the chain itself."
    dependsOn :=
      [ "IUT-I.hodge-theater-history-composition",
        "IUT-I.theta-link-graph-automorphism-reduction",
        "IUT-I.hodge-theater-family-source-laws" ] }

end LeanFormal.IUT.Audit
