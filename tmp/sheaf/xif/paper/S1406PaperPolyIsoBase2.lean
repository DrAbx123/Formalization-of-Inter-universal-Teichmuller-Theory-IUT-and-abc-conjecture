import tmp.sheaf.xif.paper.S1264SourceCapsuleInd1Actual
import tmp.sheaf.xif.paper.S1313IntegralLogShellContractActual
import tmp.sheaf.xif.paper.S1318IntegralCapsuleZpHomActual

/-!
# S1406 base: the paper poly-isomorphism is an Ind1/Ind2 orbit

In IUT III a poly-isomorphism is explicitly defined as an orbit of isomorphisms
with respect to the independent actions of {±1} on the direct factors, together
with the Ind1 automorphisms of the procession.  At the data layer this means:

* the first field (the label permutation) ranges over the capsule permutations
  (the Ind1 part, represented by the full data-layer permutation group);
* the second field is an independent sign choice on each direct factor (Ind2).

The paper object is therefore a set of representatives, not a single
PolyIsoAction.  The files S1264/S1313/S1318 construct single representatives:

* S1264: completion-field shell, label reversal, reflexive shell equivalences;
* S1313: integral log-shell lattice, label reversal, reflexive shell
  equivalences;
* S1318: valuation-dependent Z_p shell, label reversal, -1 on each shell.

This file proves that each of these is a member of the corresponding full
poly-isomorphism orbit, that the orbit is not a singleton, and that the first
fields are exactly Fin.revPerm.  It then proves the exact source-agreement
criterion for that first field: the source permutation I.family.permutation
induces Fin.revPerm on the canonical capsule slice precisely when the
SourcePermutationCapsuleLift.index_compat equation of S1264 holds.  The actual
actions agree with the actual source-level Ind1 candidate ind1Candidate.

No Classical.choice is used to select a poly-isomorphism; the label
permutations and sign choices are explicit data.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1406PaperPolyIsoActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual
open LeanFormal.IUT.XiFPaper.S1313IntegralLogShellContractActual
open LeanFormal.IUT.XiFPaper.S1318IntegralCapsuleZpHomActual
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui uR uVQ uPlace uShell uM

local instance factPrimeOfPrimeGeFive (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

/-! ## 1. Independent sign choices -/

/-- The two R-linear automorphisms -1 and +1 of an R-module. -/
def signEquiv (R : Type uR) [Ring R] (M : Type uM) [AddCommGroup M] [Module R M]
    (b : Bool) : M ≃ₗ[R] M :=
  if b then LinearEquiv.neg R else LinearEquiv.refl R M

@[simp] theorem signEquiv_false (R : Type uR) [Ring R] (M : Type uM)
    [AddCommGroup M] [Module R M] :
    signEquiv R M false = LinearEquiv.refl R M := rfl

@[simp] theorem signEquiv_true (R : Type uR) [Ring R] (M : Type uM)
    [AddCommGroup M] [Module R M] :
    signEquiv R M true = LinearEquiv.neg R := rfl

/-- An independent sign choice on each direct factor (i, vQ). -/
abbrev SignChoice (j : Nat) (VQ : Type uVQ) : Type uVQ :=
  (i : Capsule j) → VQ → Bool

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 2. The integral-lattice action of S1313 -/

/-- The data-layer full poly-isomorphism on S1313's integral log-shell family:
Ind1 label permutations and Ind2 independent signs. -/
def paperFullPolyIsoIntegral (j : Nat) :
    Set (PolyIsoAction (integralLogShellFamily I j)) :=
  {A | ∃ σ : Capsule j ≃ Capsule j,
    ∃ ε : SignChoice j (ActualIntegralValuation),
      A.labelPerm = σ ∧
        ∀ i vQ v, A.shellEquiv i vQ v =
          signEquiv ℤ (↥(actualIntegralLogShell I vQ v)) (ε i vQ)}

/-- The action obtained from an explicit Ind1 permutation and Ind2 sign
choice. -/
def signActionIntegral (j : Nat) (σ : Capsule j ≃ Capsule j)
    (ε : SignChoice j (ActualIntegralValuation)) :
    PolyIsoAction (integralLogShellFamily I j) where
  labelPerm := σ
  shellEquiv := fun i vQ v =>
    signEquiv ℤ (↥(actualIntegralLogShell I vQ v)) (ε i vQ)

theorem signActionIntegral_mem (j : Nat) (σ : Capsule j ≃ Capsule j)
    (ε : SignChoice j (ActualIntegralValuation)) :
    signActionIntegral I j σ ε ∈ paperFullPolyIsoIntegral I j := by
  refine ⟨σ, ε, rfl, ?_⟩
  intro i vQ v
  rfl

/-- Exact characterisation of the paper's full poly-isomorphism as the range
of explicit (Ind1, Ind2) data. -/
theorem mem_paperFullPolyIsoIntegral_iff (j : Nat)
    {A : PolyIsoAction (integralLogShellFamily I j)} :
    A ∈ paperFullPolyIsoIntegral I j ↔
      ∃ σ : Capsule j ≃ Capsule j,
        ∃ ε : SignChoice j (ActualIntegralValuation),
          A = signActionIntegral I j σ ε := by
  constructor
  · rintro ⟨σ, ε, hσ, hε⟩
    refine ⟨σ, ε, ?_⟩
    cases A with
    | mk lp se =>
      simp only at hσ hε ⊢
      subst hσ
      have hse : (fun i vQ v =>
          signEquiv ℤ (↥(actualIntegralLogShell I vQ v)) (ε i vQ)) = se := by
        funext i vQ v
        exact (hε i vQ v).symm
      subst hse
      rfl
  · rintro ⟨σ, ε, rfl⟩
    exact signActionIntegral_mem I j σ ε

/-- The actual integral action of S1313 is the (label reversal, all-+1)
representative. -/
theorem integralLogShellPolyIso_mem (j : Nat) :
    integralLogShellPolyIso I j ∈ paperFullPolyIsoIntegral I j := by
  refine ⟨Fin.revPerm, (fun _ _ => false), rfl, ?_⟩
  intro i vQ v
  rfl

/-- Exact first field of S1313's actual action. -/
@[simp] theorem integralLogShellPolyIso_labelPerm (j : Nat) :
    (integralLogShellPolyIso I j).labelPerm = Fin.revPerm := rfl

/-- Exact first field of S1313's filled contract. -/
@[simp] theorem actualIntegralCapsuleContract_polyIso_labelPerm
    (j : Fin (capsuleLevels l)) :
    ((actualIntegralCapsuleContract I).polyIso j).labelPerm = Fin.revPerm := rfl

/-- The label reversal is not the identity already on the two-element capsule. -/
theorem finRevPerm_ne_refl_one :
    (Fin.revPerm : Capsule 1 ≃ Capsule 1) ≠ Equiv.refl (Capsule 1) := by
  intro h
  have h0 := congrArg (fun e => e (0 : Capsule 1)) h
  simp [Fin.revPerm_apply, Fin.rev] at h0

/-- The paper's full poly-isomorphism is not a single action. -/
theorem paperFullPolyIsoIntegral_not_singleton :
    paperFullPolyIsoIntegral I 1 ≠
      ({integralLogShellPolyIso I 1} :
        Set (PolyIsoAction (integralLogShellFamily I 1))) := by
  intro h
  have hmemOrbit : PolyIsoAction.refl (integralLogShellFamily I 1) ∈
      paperFullPolyIsoIntegral I 1 := by
    refine ⟨Equiv.refl (Capsule 1), (fun _ _ => false), rfl, ?_⟩
    intro i vQ v
    rfl
  have hmem : PolyIsoAction.refl (integralLogShellFamily I 1) ∈
      ({integralLogShellPolyIso I 1} :
        Set (PolyIsoAction (integralLogShellFamily I 1))) := by
    rw [← h]
    exact hmemOrbit
  have heq : PolyIsoAction.refl (integralLogShellFamily I 1) =
      integralLogShellPolyIso I 1 := by
    simpa using hmem
  have hlabel : (PolyIsoAction.refl (integralLogShellFamily I 1)).labelPerm ≠
      (integralLogShellPolyIso I 1).labelPerm := by
    rw [integralLogShellPolyIso_labelPerm]
    simpa [PolyIsoAction.refl] using (Ne.symm finRevPerm_ne_refl_one)
  exact hlabel (congrArg PolyIsoAction.labelPerm heq)

/-! ## 3. The completion-field action of S1264 -/

/-- The data-layer full poly-isomorphism on S1264's completion field family. -/
def paperFullPolyIsoCompletion (j : Nat) :
    Set (PolyIsoAction (actualLogShellFamily I j)) :=
  {A | ∃ σ : Capsule j ≃ Capsule j,
    ∃ ε : SignChoice j (S1264SourceCapsuleInd1Actual.RationalPlaceAt l),
      A.labelPerm = σ ∧
        ∀ i vQ v, A.shellEquiv i vQ v =
          signEquiv ℚ_[l.value] (CommonPrimeCompletion v) (ε i vQ)}

/-- The action obtained from an explicit Ind1 permutation and Ind2 sign
choice. -/
def signActionCompletion (j : Nat) (σ : Capsule j ≃ Capsule j)
    (ε : SignChoice j (S1264SourceCapsuleInd1Actual.RationalPlaceAt l)) :
    PolyIsoAction (actualLogShellFamily I j) where
  labelPerm := σ
  shellEquiv := fun i vQ v =>
    signEquiv ℚ_[l.value] (CommonPrimeCompletion v) (ε i vQ)

theorem signActionCompletion_mem (j : Nat) (σ : Capsule j ≃ Capsule j)
    (ε : SignChoice j (S1264SourceCapsuleInd1Actual.RationalPlaceAt l)) :
    signActionCompletion I j σ ε ∈ paperFullPolyIsoCompletion I j := by
  refine ⟨σ, ε, rfl, ?_⟩
  intro i vQ v
  rfl

/-- The actual completion-field action of S1264 is the
(label reversal, all-+1) representative. -/
theorem actualPolyIso_mem (j : Nat) :
    actualPolyIso I j ∈ paperFullPolyIsoCompletion I j := by
  refine ⟨Fin.revPerm, (fun _ _ => false), rfl, ?_⟩
  intro i vQ v
  rfl

/-- Exact first field of S1264's actual action. -/
@[simp] theorem actualPolyIso_labelPerm (j : Nat) :
    (actualPolyIso I j).labelPerm = Fin.revPerm := rfl

/-- Exact first field of S1264's filled contract. -/
@[simp] theorem actualContract_polyIso_labelPerm
    (n : Int) (j : Fin (capsuleLevels l)) :
    ((actualContract I n).polyIso j).labelPerm = Fin.revPerm := rfl

/-! ## 4. The valuation-dependent Z_p action of S1318 -/

/-- The sign automorphism of S1318's actual Z_p-shell at a valuation. -/
def zpSignShell (vQ : S1270NontrivialCapsuleActual.ActualValuation)
    (v : S1270NontrivialCapsuleActual.actualPlace I vQ) (b : Bool) :
    actualZpShell I vQ v ≃ₗ[actualZpR vQ] actualZpShell I vQ v := by
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  exact signEquiv (actualZpR vQ) (actualZpShell I vQ v) b

/-- The data-layer full poly-isomorphism on S1318's valuation-dependent
family. -/
def paperFullPolyIsoZp (j : Nat) :
    Set (PolyIsoActionZp (actualZpLogShellFamily I j)) :=
  {A | ∃ σ : Capsule j ≃ Capsule j,
    ∃ ε : SignChoice j (S1270NontrivialCapsuleActual.ActualValuation),
      A.labelPerm = σ ∧
        ∀ i vQ v, A.shellEquiv i vQ v = zpSignShell I vQ v (ε i vQ)}

/-- The action obtained from an explicit Ind1 permutation and Ind2 sign
choice. -/
def signActionZp (j : Nat) (σ : Capsule j ≃ Capsule j)
    (ε : SignChoice j (S1270NontrivialCapsuleActual.ActualValuation)) :
    PolyIsoActionZp (actualZpLogShellFamily I j) where
  labelPerm := σ
  shellEquiv := fun i vQ v => zpSignShell I vQ v (ε i vQ)

theorem signActionZp_mem (j : Nat) (σ : Capsule j ≃ Capsule j)
    (ε : SignChoice j (S1270NontrivialCapsuleActual.ActualValuation)) :
    signActionZp I j σ ε ∈ paperFullPolyIsoZp I j := by
  refine ⟨σ, ε, rfl, ?_⟩
  intro i vQ v
  rfl

/-- The actual Z_p action of S1318 is the (label reversal, all--1)
representative. -/
theorem actualZpPolyIso_mem (j : Nat) :
    actualZpPolyIso I j ∈ paperFullPolyIsoZp I j := by
  refine ⟨Fin.revPerm, (fun _ _ => true), rfl, ?_⟩
  intro i vQ v
  simp [zpSignShell, signEquiv, actualZpPolyIso]

/-- Exact first field of S1318's actual action. -/
@[simp] theorem actualZpPolyIso_labelPerm (j : Nat) :
    (actualZpPolyIso I j).labelPerm = Fin.revPerm := rfl

/-- Exact first field of S1318's filled contract. -/
@[simp] theorem actualZpCapsuleContract_polyIso_labelPerm
    (j : Fin (capsuleLevels l)) :
    ((actualZpCapsuleContract I).polyIso j).labelPerm = Fin.revPerm := rfl

/-! ## 5. Exact first-field/source agreement -/

/-- The exact condition under which the first field Fin.revPerm is induced by
the source permutation I.family.permutation on the canonical capsule slice
i |-> (i,n).  This is precisely the index_compat field of S1264's
SourcePermutationCapsuleLift. -/
def SourceLabelAgreement (n : Int) (j : Fin (capsuleLevels l)) : Prop :=
  ∀ i : Capsule j.val,
    I.index_equiv (I.family.permutation (I.indexOf (Int.ofNat i.val) n)) =
      (((Fin.revPerm i).val : Int), n)

theorem sourcePermutationCapsuleLift_revPerm_iff
    (n : Int) (j : Fin (capsuleLevels l)) :
    (∃ L : SourcePermutationCapsuleLift I n j, L.perm = Fin.revPerm) ↔
      SourceLabelAgreement I n j := by
  constructor
  · rintro ⟨L, hL⟩ i
    have h := L.index_compat i
    simpa [SourceLabelAgreement, hL, canonicalCapsuleTheaterAssignment] using h
  · intro h
    refine ⟨⟨Fin.revPerm, ?_⟩, rfl⟩
    intro i
    simpa [SourceLabelAgreement, canonicalCapsuleTheaterAssignment] using h i

/-- The exact source-agreement criterion for S1264's actual first field. -/
theorem actualPolyIso_source_agreement_iff
    (n : Int) (j : Fin (capsuleLevels l)) :
    (∃ L : SourcePermutationCapsuleLift I n j,
        L.perm = (actualPolyIso I j.val).labelPerm) ↔
      SourceLabelAgreement I n j := by
  rw [actualPolyIso_labelPerm]
  exact sourcePermutationCapsuleLift_revPerm_iff I n j

/-- The exact source-agreement criterion for S1313's actual first field. -/
theorem integralLogShellPolyIso_source_agreement_iff
    (n : Int) (j : Fin (capsuleLevels l)) :
    (∃ L : SourcePermutationCapsuleLift I n j,
        L.perm = (integralLogShellPolyIso I j.val).labelPerm) ↔
      SourceLabelAgreement I n j := by
  rw [integralLogShellPolyIso_labelPerm]
  exact sourcePermutationCapsuleLift_revPerm_iff I n j

/-- The exact source-agreement criterion for S1318's actual first field. -/
theorem actualZpPolyIso_source_agreement_iff
    (n : Int) (j : Fin (capsuleLevels l)) :
    (∃ L : SourcePermutationCapsuleLift I n j,
        L.perm = (actualZpPolyIso I j.val).labelPerm) ↔
      SourceLabelAgreement I n j := by
  rw [actualZpPolyIso_labelPerm]
  exact sourcePermutationCapsuleLift_revPerm_iff I n j

/-- The first field of S1264's actual action agrees with the actual source-level
Ind1 candidate, whose permutation is Fin.revPerm. -/
theorem actualPolyIso_labelPerm_eq_ind1Candidate_perm
    (n : Int) (j : Fin (capsuleLevels l)) :
    (actualPolyIso I j.val).labelPerm = (ind1Candidate I n j).perm := rfl

/-- Similarly, S1313's and S1318's first fields agree with the same actual
source-level Ind1 permutation. -/
theorem integralLogShellPolyIso_labelPerm_eq_ind1Candidate_perm
    (n : Int) (j : Fin (capsuleLevels l)) :
    (integralLogShellPolyIso I j.val).labelPerm = (ind1Candidate I n j).perm := rfl

theorem actualZpPolyIso_labelPerm_eq_ind1Candidate_perm
    (n : Int) (j : Fin (capsuleLevels l)) :
    (actualZpPolyIso I j.val).labelPerm = (ind1Candidate I n j).perm := rfl

end LeanFormal.IUT.XiFPaper.S1406PaperPolyIsoActual

end
