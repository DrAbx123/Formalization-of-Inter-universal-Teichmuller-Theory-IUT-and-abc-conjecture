/-
  Reduction pass for the Theta-link displacement and the Z-translation laws
  of the Frobenius-picture chain.

  Paper anchors (`D:\lean\papers\motizuki_corpus\text\Inter-universal
  Teichmuller Theory I.txt`):

  * Corollary 3.8 (lines 5039--5064): for a fixed collection of initial
    Theta-data, let `{nHT^Theta}_{n in Z}` be a collection of *distinct*
    Theta-Hodge theaters indexed by the integers; applying Corollary 3.7 (i)
    with `†HT^Theta := nHT^Theta` and `‡HT^Theta := (n+1)HT^Theta` yields an
    infinite chain of Theta-linked Theta-Hodge theaters.  The oriented graph
    carries a natural action by Z -- a *translation symmetry* -- but it does
    *not* permit arbitrary permutation symmetries; the text's explicit example
    is that no automorphism switches two adjacent vertices while fixing the
    remaining vertices (`Frobenius-like`, "order-conscious").
  * Remark 3.8.1 (i) (lines 5068--5087, Fig. 3.1): the Theta-link maps
    `n Theta_v |-> (n+1) q_v` for `v in V_bad`.

  Frozen obligation addressed by this file (new in this pass):
  `IUT-I.theta-link-displacement-reduction`.  Consumers: D3.1
  (`IUTIII\Theorem311\SourceOriginalInput.lean:41-46`), Theorem 3.11 source
  chain (`IUTIII\Theorem311\SourceH1H2Construction.lean:272-277`), and
  `SourceHodgeTheaterBridge` (`IUTIII\Theorem311\SourceHodgeTheaterBridge.lean`).

  Proved in this file:

  1. The theta-to-q displacement predicate with its identity/symmetry/
     composition laws, and the theorem that every Theta-link carries the
     displacement (both q and scale components).
  2. For any Z-indexed chain of distinct Theta-Hodge theaters with
     consecutive Theta-links: adjacent members are distinct; the chain is not
     constant; the q and scale parameters are constant along the whole chain
     (two-sided transfer); the k-fold link iterate exists and carries the
     q/scale transfer.
  3. Chain rigidity: the only label-preserving index permutation is the
     identity; the adjacent transposition and the shift `n |-> n+1` are not
     label-preserving.
  4. The automorphisms of the successor structure on Z are exactly the
     translations: every step-preserving permutation is `n |-> n+k`; the
     translations form the Z-action (apply/zero/composition/inverse laws);
     the adjacent transposition is not step-preserving, matching Corollary
     3.8's explicit exclusion.
  5. Finite witnesses: the two-member Bool family (advance-map displacement,
     displacement across distinct theaters, swap not label-preserving) and a
     one-member Unit family (every index permutation is trivial).

  Reductions (explicitly marked; none of these is the original statement):

  * The chain contract fixes one chosen Theta-link between consecutive
    theaters; Corollary 3.7 (i) gives a nonempty *set* of poly-isomorphisms,
    one choice of which is a Theta-link.
  * The carrier collapses the q-side and the Theta-side of the Frobenius data
    into the single `thetaPacket` field; the displacement `n Theta_v |->
    (n+1) q_v` is therefore represented by the q-transport of the link, and
    the scheme theory "between q_v and Theta_v" (Fig. 3.1) is not modeled.
  * "Translation symmetry" is formalized as: the translations act on the
    index (apply/zero/composition/inverse), they are step-preserving, and
    conversely every step-preserving permutation is a translation.  The
    ordered graph Gamma itself (nodes plus arrows as a structure) and a
    Z-action on it by graph automorphisms are not formalized.
  * "No arbitrary permutation symmetries" is formalized as: label-preserving
    permutations are trivial (distinctness), and the adjacent switch is not
    step-preserving.  The source's statement is about graph automorphisms of
    Gamma; we prove the label/step-level counterparts.
  * The witnesses are finite (Bool) or degenerate (Unit); the existence of the
    chain `{nHT^Theta}` from arbitrary initial Theta-data remains card C1, and
    the arithmetic-geometric realization of the displacement remains card C2.
-/

import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamilyLawsReduction
import Init.Omega

set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon

/-! ## 1. The theta-to-q displacement (Remark 3.8.1 (i)) -/

/-- The contract shadow of `n Theta_v |-> (n+1) q_v`: a link carries the
theta-side q parameter of its source to the q parameter of its target. -/
def ThetaQDisplacement {l : PrimeGeFive} {V : Type uv}
    (A B : HodgeTheater.{ua, uv, upi, umon} l V) : Prop :=
  A.thetaPacket.q = B.thetaPacket.q

/-- The scale-parameter component of the displacement, at a signed label. -/
def ThetaScaleDisplacement {l : PrimeGeFive} {V : Type uv}
    (A B : HodgeTheater.{ua, uv, upi, umon} l V) (j : SignedLabel l.value) : Prop :=
  A.thetaPacket.scale j = B.thetaPacket.scale j

theorem hodgeTheaterLink_displacement {l : PrimeGeFive} {V : Type uv}
    {A B : HodgeTheater.{ua, uv, upi, umon} l V} (L : HodgeTheaterLink A B) :
    ThetaQDisplacement A B :=
  L.theta_q_eq

theorem hodgeTheaterLink_scaleDisplacement {l : PrimeGeFive} {V : Type uv}
    {A B : HodgeTheater.{ua, uv, upi, umon} l V} (L : HodgeTheaterLink A B)
    (j : SignedLabel l.value) : ThetaScaleDisplacement A B j :=
  L.theta_scale_eq j

theorem thetaQDisplacement_refl {l : PrimeGeFive} {V : Type uv}
    (A : HodgeTheater.{ua, uv, upi, umon} l V) : ThetaQDisplacement A A := rfl

theorem thetaQDisplacement_symm {l : PrimeGeFive} {V : Type uv}
    {A B : HodgeTheater.{ua, uv, upi, umon} l V} (h : ThetaQDisplacement A B) :
    ThetaQDisplacement B A :=
  h.symm

theorem thetaQDisplacement_trans {l : PrimeGeFive} {V : Type uv}
    {A B C : HodgeTheater.{ua, uv, upi, umon} l V}
    (h₁ : ThetaQDisplacement A B) (h₂ : ThetaQDisplacement B C) :
    ThetaQDisplacement A C :=
  h₁.trans h₂

theorem thetaScaleDisplacement_refl {l : PrimeGeFive} {V : Type uv}
    (A : HodgeTheater.{ua, uv, upi, umon} l V) (j : SignedLabel l.value) :
    ThetaScaleDisplacement A A j := rfl

theorem thetaScaleDisplacement_symm {l : PrimeGeFive} {V : Type uv}
    {A B : HodgeTheater.{ua, uv, upi, umon} l V} {j : SignedLabel l.value}
    (h : ThetaScaleDisplacement A B j) : ThetaScaleDisplacement B A j :=
  h.symm

theorem thetaScaleDisplacement_trans {l : PrimeGeFive} {V : Type uv}
    {A B C : HodgeTheater.{ua, uv, upi, umon} l V} {j : SignedLabel l.value}
    (h₁ : ThetaScaleDisplacement A B j) (h₂ : ThetaScaleDisplacement B C j) :
    ThetaScaleDisplacement A C j :=
  h₁.trans h₂

/-! ## 2. The Frobenius-picture chain (Corollary 3.8) -/

/-- A Frobenius-picture chain: distinct Theta-Hodge theaters indexed by the
integers, with a Theta-link between consecutive theaters. -/
structure SourceThetaLinkChain (l : PrimeGeFive) (V : Type uv) where
  theater : Int → HodgeTheater.{ua, uv, upi, umon} l V
  distinct : Function.Injective theater
  step : ∀ n : Int, HodgeTheaterLink (theater n) (theater (n + 1))

namespace SourceThetaLinkChain

variable {l : PrimeGeFive} {V : Type uv}

theorem step_thetaQ (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (n : Int) :
    (C.theater n).thetaPacket.q = (C.theater (n + 1)).thetaPacket.q :=
  (C.step n).theta_q_eq

theorem step_scale (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (n : Int)
    (j : SignedLabel l.value) :
    (C.theater n).thetaPacket.scale j = (C.theater (n + 1)).thetaPacket.scale j :=
  (C.step n).theta_scale_eq j

theorem step_displacement (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V)
    (n : Int) : ThetaQDisplacement (C.theater n) (C.theater (n + 1)) :=
  (C.step n).theta_q_eq

theorem adjacent_ne (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (n : Int) :
    C.theater n ≠ C.theater (n + 1) := by
  intro h
  have : n = n + 1 := C.distinct h
  omega

theorem no_constant_theater (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V)
    (T : HodgeTheater.{ua, uv, upi, umon} l V) :
    ¬ (∀ n : Int, C.theater n = T) := by
  intro hT
  have h01 : C.theater 0 = C.theater 1 := by rw [hT 0, hT 1]
  have : (0 : Int) = 1 := C.distinct h01
  omega

theorem thetaQ_eq_of_le (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V)
    {m n : Int} (h : m ≤ n) :
    (C.theater m).thetaPacket.q = (C.theater n).thetaPacket.q := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n - m by omega)
  have hn : n = m + (k : Int) := by omega
  subst hn
  clear h hk
  induction k with
  | zero => simp
  | succ k ih =>
      have hidx : m + ((k + 1 : Nat) : Int) = (m + (k : Int)) + 1 := by omega
      rw [hidx]
      exact ih.trans (C.step_thetaQ (m + (k : Int)))

theorem thetaQ_eq (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (m n : Int) :
    (C.theater m).thetaPacket.q = (C.theater n).thetaPacket.q := by
  by_cases h : m ≤ n
  · exact C.thetaQ_eq_of_le h
  · exact (C.thetaQ_eq_of_le (le_of_lt (not_le.mp h))).symm

theorem thetaScale_eq_of_le (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V)
    {m n : Int} (h : m ≤ n) (j : SignedLabel l.value) :
    (C.theater m).thetaPacket.scale j = (C.theater n).thetaPacket.scale j := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n - m by omega)
  have hn : n = m + (k : Int) := by omega
  subst hn
  clear h hk
  induction k with
  | zero => simp
  | succ k ih =>
      have hidx : m + ((k + 1 : Nat) : Int) = (m + (k : Int)) + 1 := by omega
      rw [hidx]
      exact ih.trans (C.step_scale (m + (k : Int)) j)

theorem thetaScale_eq (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V)
    (m n : Int) (j : SignedLabel l.value) :
    (C.theater m).thetaPacket.scale j = (C.theater n).thetaPacket.scale j := by
  by_cases h : m ≤ n
  · exact C.thetaScale_eq_of_le h j
  · exact (C.thetaScale_eq_of_le (le_of_lt (not_le.mp h)) j).symm

/-- The k-fold composite of the chain steps: the Z-translation by `k` sends
position `n` to position `n + k`. -/
def linkIterate (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (n : Int) :
    (k : Nat) → HodgeTheaterLink (C.theater n) (C.theater (n + (k : Int)))
  | 0 =>
      Eq.mp (congrArg (fun i => HodgeTheaterLink (C.theater n) (C.theater i))
        (by simp : n = n + ((0 : Nat) : Int)))
        (HodgeTheaterLink.refl (C.theater n))
  | k + 1 =>
      Eq.mp (congrArg (fun i => HodgeTheaterLink (C.theater n) (C.theater i))
        (by omega : (n + (k : Int)) + 1 = n + ((k + 1 : Nat) : Int)))
        (HodgeTheaterLink.trans (linkIterate C n k) (C.step (n + (k : Int))))

theorem linkIterate_thetaQ (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V)
    (n : Int) (k : Nat) :
    (C.theater n).thetaPacket.q = (C.theater (n + (k : Int))).thetaPacket.q :=
  (linkIterate C n k).theta_q_eq

theorem linkIterate_scale (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V)
    (n : Int) (k : Nat) (j : SignedLabel l.value) :
    (C.theater n).thetaPacket.scale j =
      (C.theater (n + (k : Int))).thetaPacket.scale j :=
  (linkIterate C n k).theta_scale_eq j

theorem index_automorphism_eq_one (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V)
    (σ : Equiv.Perm Int) (hσ : ∀ n : Int, C.theater (σ n) = C.theater n) :
    σ = 1 := by
  have hn : ∀ n : Int, σ n = n := fun n => C.distinct (hσ n)
  exact Equiv.ext hn

theorem adjacent_swap_not_preserving (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) :
    ¬ (∀ n : Int, C.theater (Equiv.swap 0 1 n) = C.theater n) := by
  intro h
  have h0 : C.theater 1 = C.theater 0 := by
    simpa [Equiv.swap_apply_left] using h 0
  have : (1 : Int) = 0 := C.distinct h0
  omega

theorem shift_not_preserving (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) :
    ¬ (∀ n : Int, C.theater (n + 1) = C.theater n) := by
  intro h
  have : (0 : Int) + 1 = 0 := C.distinct (h 0)
  omega

end SourceThetaLinkChain

/-! ## 3. The Z-translation symmetry and its classification -/

/-- Translation of the integer index by `k`: the contract form of the
Z-translation symmetry of the Frobenius-picture chain (Corollary 3.8). -/
def chainTranslation (k : Int) : Equiv.Perm Int where
  toFun n := n + k
  invFun n := n - k
  left_inv := by intro n; change n + k - k = n; omega
  right_inv := by intro n; change n - k + k = n; omega

@[simp] theorem chainTranslation_apply (k n : Int) : chainTranslation k n = n + k := rfl

theorem chainTranslation_zero : chainTranslation 0 = 1 := by
  ext n
  change n + 0 = n
  omega

theorem chainTranslation_comp (k l : Int) :
    (chainTranslation l) ∘ (chainTranslation k) = chainTranslation (k + l) := by
  funext n
  simp [chainTranslation_apply]
  omega

theorem chainTranslation_symm (k : Int) :
    (chainTranslation k).symm = chainTranslation (-k) := by
  ext n
  change n - k = n + -k
  omega

/-- A permutation of the chain positions preserves the successor relation
(the contract form of an automorphism of the oriented graph Gamma). -/
def ChainStepPreserving (σ : Equiv.Perm Int) : Prop :=
  ∀ n : Int, σ (n + 1) = σ n + 1

theorem chainTranslation_stepPreserving (k : Int) :
    ChainStepPreserving (chainTranslation k) := by
  intro n
  change (n + 1) + k = n + k + 1
  omega

theorem chainStepPreserving_apply_of_nonneg (σ : Equiv.Perm Int)
    (hσ : ChainStepPreserving σ) {n : Int} (hn : 0 ≤ n) :
    σ n = n + σ 0 := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hn
  subst hk
  clear hn
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := hσ ((k : Int))
      have hidx : ((k : Int) + 1) = ((k + 1 : Nat) : Int) := by omega
      rw [← hidx]
      rw [hstep]
      omega

theorem chainStepPreserving_apply_of_nonpos (σ : Equiv.Perm Int)
    (hσ : ChainStepPreserving σ) {n : Int} (hn : n ≤ 0) :
    σ n = n + σ 0 := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -n by omega)
  have hn' : n = -(k : Int) := by omega
  subst hn'
  clear hn hk
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := hσ (-((k : Int) + 1))
      have hidx : -((k : Int) + 1) + 1 = -(k : Int) := by omega
      rw [hidx] at hstep
      have hidx2 : -((k : Int) + 1) = -(((k + 1 : Nat) : Int)) := by omega
      rw [← hidx2]
      omega

/-- The automorphisms of the successor structure on Z are exactly the
translations: every step-preserving permutation is `n |-> n + k`. -/
theorem chainStepPreserving_eq_translation (σ : Equiv.Perm Int)
    (hσ : ChainStepPreserving σ) :
    ∃ k : Int, ∀ n : Int, σ n = n + k := by
  refine ⟨σ 0, fun n => ?_⟩
  by_cases hn : 0 ≤ n
  · exact chainStepPreserving_apply_of_nonneg σ hσ hn
  · exact chainStepPreserving_apply_of_nonpos σ hσ (le_of_lt (not_le.mp hn))

/-- Corollary 3.8's explicit example: the transposition of two adjacent
positions is not an automorphism of the chain structure. -/
theorem adjacent_swap_not_chainStepPreserving :
    ¬ ChainStepPreserving (Equiv.swap (0 : Int) 1) := by
  intro h
  obtain ⟨k, hk⟩ := chainStepPreserving_eq_translation (Equiv.swap (0 : Int) 1) h
  have h0 : (1 : Int) = 0 + k := by simpa [Equiv.swap_apply_left] using hk 0
  have h1 : (0 : Int) = 1 + k := by simpa [Equiv.swap_apply_right] using hk 1
  omega

/-! ## 4. Finite witness: displacement on the two-member family -/

/-- The finite advance map: `false` advances to `true`; `true` is terminal. -/
def twoTheaterWitnessAdvance : Bool → Bool := fun _ => true

theorem twoTheaterWitnessAdvance_false : twoTheaterWitnessAdvance false = true := rfl

theorem twoTheaterWitnessAdvance_true : twoTheaterWitnessAdvance true = true := rfl

theorem twoTheaterWitness_displacement_at (l : PrimeGeFive) (b : Bool) :
    ThetaQDisplacement
      ((finiteIntegralTwoTheaterFamily l).theater b)
      ((finiteIntegralTwoTheaterFamily l).theater (twoTheaterWitnessAdvance b)) := by
  cases b
  · exact ((finiteIntegralTwoTheaterFamily l).link false true).theta_q_eq
  · exact thetaQDisplacement_refl ((finiteIntegralTwoTheaterFamily l).theater true)

theorem twoTheaterWitness_displacement_separates (l : PrimeGeFive) :
    ThetaQDisplacement ((finiteIntegralTwoTheaterFamily l).theater false)
        ((finiteIntegralTwoTheaterFamily l).theater true) ∧
      (finiteIntegralTwoTheaterFamily l).theater false ≠
        (finiteIntegralTwoTheaterFamily l).theater true :=
  ⟨((finiteIntegralTwoTheaterFamily l).link false true).theta_q_eq,
    finiteIntegralTwoTheaterFamily_theater_ne l⟩

theorem twoTheaterWitness_swap_not_preserving (l : PrimeGeFive) :
    ¬ (∀ b : Bool,
        (finiteIntegralTwoTheaterFamily l).theater (Equiv.swap false true b) =
          (finiteIntegralTwoTheaterFamily l).theater b) := by
  intro h
  have h0 : (finiteIntegralTwoTheaterFamily l).theater true =
      (finiteIntegralTwoTheaterFamily l).theater false := by
    simpa [Equiv.swap_apply_left] using h false
  exact finiteIntegralTwoTheaterFamily_theater_ne l h0.symm

/-! ## 5. Degenerate witness: the one-member family -/

/-- The one-member family: a single theater; its index has no nontrivial
permutations, and every pair of members shares one theta packet. -/
def unitHodgeTheaterFamily (l : PrimeGeFive) (V : Type uv)
    (T : HodgeTheater.{ua, uv, upi, umon} l V) :
    SourceHodgeTheaterFamily.{ua, uv, upi, umon, 0} l V where
  index := Unit
  theater := fun _ => T
  distinct := fun _ _ _ => Subsingleton.elim _ _
  link := fun _ _ => HodgeTheaterLink.refl T
  link_refl := fun _ => rfl
  link_symm := fun _ _ => rfl
  link_trans := fun _ _ _ => rfl
  permutation := Equiv.refl Unit
  permutationLink := fun _ => HodgeTheaterLink.refl T
  permutation_naturality := fun _ _ => rfl

theorem unitHodgeTheaterFamily_index_perm_eq_one (l : PrimeGeFive) (V : Type uv)
    (T : HodgeTheater.{ua, uv, upi, umon} l V)
    (σ : Equiv.Perm (unitHodgeTheaterFamily l V T).index) : σ = 1 := by
  haveI : Subsingleton (unitHodgeTheaterFamily l V T).index :=
    ⟨fun a b => by cases a; cases b; rfl⟩
  exact Equiv.ext (fun u => Subsingleton.elim _ _)

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def thetaLinkDisplacementReduction : Obligation :=
  { id := "IUT-I.theta-link-displacement-reduction"
    source :=
      "IUT I: Corollary 3.8 (Frobenius-picture chain and its Z-translation " ++
        "symmetry); Remark 3.8.1 (i) and Fig. 3.1 (n Theta_v |-> (n+1) q_v)"
    status := VerificationStatus.interface
    note :=
      "Reduction pass for the Theta-link displacement and translation laws. " ++
        "Proved here: (1) the theta-to-q displacement predicate with its " ++
        "identity/symmetry/composition laws, and the theorem that every link " ++
        "carries the displacement; (2) for any Z-indexed chain of distinct " ++
        "theaters with consecutive Theta-links, adjacent members are distinct, " ++
        "the chain is not constant, and the q and scale parameters are " ++
        "constant along the chain (two-sided transfer from consecutive steps); " ++
        "the k-fold link iterate exists and carries the q/scale transfer; " ++
        "(3) chain rigidity: the only label-preserving index permutation is " ++
        "the identity, and the adjacent transposition and the shift n |-> n+1 " ++
        "are not label-preserving; (4) the automorphisms of the successor " ++
        "structure on Z are exactly the translations (every step-preserving " ++
        "permutation is n |-> n+k), the translations form the Z-action " ++
        "(apply/zero/composition/inverse laws), and the adjacent transposition " ++
        "is not step-preserving, matching Corollary 3.8's exclusion; (5) finite " ++
        "witnesses: advance-map displacement and swap non-preservation on the " ++
        "two-member Bool family, and a one-member Unit family whose index " ++
        "permutations are all trivial. Not proved (source cards): the " ++
        "existence of the chain {nHT^Theta} from arbitrary initial Theta-data " ++
        "(card C1); the arithmetic-geometric realization of the displacement " ++
        "between the q-side and the Theta-side of the Frobenius data (the " ++
        "carrier collapses the two sides; card C2); and the ordered graph " ++
        "Gamma as a structure carrying the full Z-action. The witnesses are " ++
        "finite and are not the source's Z-chain."
    dependsOn :=
      [ "IUT-I.hodge-theater-family-source-laws",
        "IUT-I.hodge-theater-histories",
        "IUT-I.hodge-theater-source" ] }

end LeanFormal.IUT.Audit
