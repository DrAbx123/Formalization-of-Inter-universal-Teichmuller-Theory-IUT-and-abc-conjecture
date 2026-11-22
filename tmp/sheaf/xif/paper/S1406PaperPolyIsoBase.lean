import tmp.sheaf.xif.paper.S1264SourceCapsuleInd1Actual
import tmp.sheaf.xif.paper.S1313IntegralLogShellContractActual
import tmp.sheaf.xif.paper.S1318IntegralCapsuleZpHomActual

/-!
# S1406 base: the paper poly-isomorphism is a sign orbit

This development records the exact relation between the "actual polyIso"
constructions of S1264/S1313/S1318 and the paper's notion of a
poly-isomorphism.  In IUT III (the passage around the construction of
log(†D⊢_v) ~> log(†F⊢×μ_v)), a poly-isomorphism is explicitly *an orbit of
isomorphisms with respect to the independent actions of {±1} on each of the
direct factors*.  Consequently the paper object is a set of representatives,
not a single PolyIsoAction.

The file therefore proves:

* the paper's full poly-isomorphism at the data layer is exactly the range of
  the independent sign choices applied to the actual action (for the same
  first field Fin.revPerm);
* the actual action is a member of that orbit;
* the orbit has at least two elements, so it is not a single action;
* the exact first field of each of the three actual actions is Fin.revPerm;
* the exact source-agreement criterion for this first field with
  I.family.permutation is the SourcePermutationCapsuleLift.index_compat
  equation of S1264, and the actual action agrees with the actual source-level
  Ind1 candidate ind1Candidate whose permutation is Fin.revPerm.

No Classical.choice is used to select a poly-isomorphism; the sign choices
are explicit Bool-valued functions.
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

/-- The paper's full poly-isomorphism on S1313's integral log-shell family:
the label permutation is fixed to Fin.revPerm, and the shell automorphisms
are the independent sign choices on the direct factors. -/
def paperFullPolyIsoIntegral (j : Nat) :
    Set (PolyIsoAction (integralLogShellFamily I j)) :=
  {A | A.labelPerm = Fin.revPerm ∧
    ∃ ε : SignChoice j (ActualIntegralValuation),
      ∀ i vQ v, A.shellEquiv i vQ v =
        signEquiv ℤ (↥(actualIntegralLogShell I vQ v)) (ε i vQ)}

/-- The action obtained from an explicit sign choice. -/
def signActionIntegral (j : Nat)
    (ε : SignChoice j (ActualIntegralValuation)) :
    PolyIsoAction (integralLogShellFamily I j) where
  labelPerm := Fin.revPerm
  shellEquiv := fun i vQ v =>
    signEquiv ℤ (↥(actualIntegralLogShell I vQ v)) (ε i vQ)

theorem signActionIntegral_mem (j : Nat)
    (ε : SignChoice j (ActualIntegralValuation)) :
    signActionIntegral I j ε ∈ paperFullPolyIsoIntegral I j := by
  refine ⟨rfl, ε, ?_⟩
  intro i vQ v
  rfl

/-- The actual integral action of S1313 is the all-+1 representative. -/
theorem integralLogShellPolyIso_mem (j : Nat) :
    integralLogShellPolyIso I j ∈ paperFullPolyIsoIntegral I j := by
  refine ⟨rfl, fun _ _ => false, ?_⟩
  intro i vQ v
  rfl

/-- The paper's full poly-isomorphism is literally the range of the
independent sign choices applied to the fixed label permutation. -/
theorem paperFullPolyIsoIntegral_eq_range (j : Nat) :
    paperFullPolyIsoIntegral I j = Set.range (signActionIntegral I j) := by
  ext A
  constructor
  · rintro ⟨hσ, ε, hε⟩
    refine ⟨ε, ?_⟩
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
  · rintro ⟨ε, rfl⟩
    exact signActionIntegral_mem I j ε

/-- Exact first field of S1313's actual action. -/
@[simp] theorem integralLogShellPolyIso_labelPerm (j : Nat) :
    (integralLogShellPolyIso I j).labelPerm = Fin.revPerm := rfl

/-- Exact first field of S1313's filled contract. -/
@[simp] theorem actualIntegralCapsuleContract_polyIso_labelPerm
    (j : Fin (capsuleLevels l)) :
    ((actualIntegralCapsuleContract I).polyIso j).labelPerm = Fin.revPerm := rfl

/-- The sign -1 and the identity differ on the actual integral lattice. -/
theorem neg_ne_refl_integralShell
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    (LinearEquiv.neg ℤ :
      ↥(actualIntegralLogShell I vQ v) ≃ₗ[ℤ]
        ↥(actualIntegralLogShell I vQ v)) ≠
      LinearEquiv.refl ℤ (↥(actualIntegralLogShell I vQ v)) := by
  intro h
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  let x : ↥(actualIntegralLogShell I vQ v) :=
    ⟨1, one_mem_integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1)⟩
  have hx : -x = x := by
    have := congrArg (fun e => e x) h
    simpa using this
  have hchar : ringChar (CommonPrimeCompletion v) ≠ 2 := by
    rw [ringChar.eq_zero]
    norm_num
  have hx0 : x = 0 :=
    (Ring.eq_self_iff_eq_zero_of_char_ne_two hchar).mp hx
  have h1 : (1 : CommonPrimeCompletion v) = 0 := by
    simpa [x] using congrArg Subtype.val hx0
  exact one_ne_zero h1

/-- The all--1 representative, which is a second element of the paper orbit. -/
def negSignActionIntegral (j : Nat) :
    PolyIsoAction (integralLogShellFamily I j) :=
  signActionIntegral I j (fun _ _ => true)

theorem negSignActionIntegral_mem (j : Nat) :
    negSignActionIntegral I j ∈ paperFullPolyIsoIntegral I j :=
  signActionIntegral_mem I j (fun _ _ => true)

/-- The all--1 representative is not the actual all-+1 action. -/
theorem negSignActionIntegral_ne
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    negSignActionIntegral I 1 ≠ integralLogShellPolyIso I 1 := by
  intro h
  have h1 : (negSignActionIntegral I 1).shellEquiv
        (⟨0, by norm_num⟩ : Capsule 1) vQ v =
      (integralLogShellPolyIso I 1).shellEquiv
        (⟨0, by norm_num⟩ : Capsule 1) vQ v :=
    congrArg (fun A => A.shellEquiv (⟨0, by norm_num⟩ : Capsule 1) vQ v) h
  have h2 : (LinearEquiv.neg ℤ :
      ↥(actualIntegralLogShell I vQ v) ≃ₗ[ℤ]
        ↥(actualIntegralLogShell I vQ v)) =
      LinearEquiv.refl ℤ (↥(actualIntegralLogShell I vQ v)) := by
    simpa [negSignActionIntegral, signActionIntegral, signEquiv,
      integralLogShellPolyIso] using h1
  exact neg_ne_refl_integralShell I vQ v h2

/-- The paper's full poly-isomorphism is not a single action. -/
theorem paperFullPolyIsoIntegral_not_singleton
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    paperFullPolyIsoIntegral I 1 ≠
      ({integralLogShellPolyIso I 1} :
        Set (PolyIsoAction (integralLogShellFamily I 1))) := by
  intro h
  have hmem : negSignActionIntegral I 1 ∈
      ({integralLogShellPolyIso I 1} :
        Set (PolyIsoAction (integralLogShellFamily I 1))) := by
    rw [← h]
    exact negSignActionIntegral_mem I 1
  have heq : negSignActionIntegral I 1 = integralLogShellPolyIso I 1 := by
    simpa using hmem
  exact negSignActionIntegral_ne I vQ v heq

/-! ## 3. The completion-field action of S1264 -/

/-- The paper's full poly-isomorphism on S1264's completion field family. -/
def paperFullPolyIsoCompletion (j : Nat) :
    Set (PolyIsoAction (actualLogShellFamily I j)) :=
  {A | A.labelPerm = Fin.revPerm ∧
    ∃ ε : SignChoice j (S1264SourceCapsuleInd1Actual.RationalPlaceAt l),
      ∀ i vQ v, A.shellEquiv i vQ v =
        signEquiv ℚ_[l.value] (CommonPrimeCompletion v) (ε i vQ)}

/-- The action obtained from an explicit sign choice. -/
def signActionCompletion (j : Nat)
    (ε : SignChoice j (S1264SourceCapsuleInd1Actual.RationalPlaceAt l)) :
    PolyIsoAction (actualLogShellFamily I j) where
  labelPerm := Fin.revPerm
  shellEquiv := fun i vQ v =>
    signEquiv ℚ_[l.value] (CommonPrimeCompletion v) (ε i vQ)

theorem signActionCompletion_mem (j : Nat)
    (ε : SignChoice j (S1264SourceCapsuleInd1Actual.RationalPlaceAt l)) :
    signActionCompletion I j ε ∈ paperFullPolyIsoCompletion I j := by
  refine ⟨rfl, ε, ?_⟩
  intro i vQ v
  rfl

/-- The actual completion-field action of S1264 is the all-+1 representative. -/
theorem actualPolyIso_mem (j : Nat) :
    actualPolyIso I j ∈ paperFullPolyIsoCompletion I j := by
  refine ⟨rfl, fun _ _ => false, ?_⟩
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

/-- The paper's full poly-isomorphism on S1318's valuation-dependent family. -/
def paperFullPolyIsoZp (j : Nat) :
    Set (PolyIsoActionZp (actualZpLogShellFamily I j)) :=
  {A | A.labelPerm = Fin.revPerm ∧
    ∃ ε : SignChoice j (S1270NontrivialCapsuleActual.ActualValuation),
      ∀ i vQ v, A.shellEquiv i vQ v = zpSignShell I vQ v (ε i vQ)}

/-- The action obtained from an explicit sign choice. -/
def signActionZp (j : Nat)
    (ε : SignChoice j (S1270NontrivialCapsuleActual.ActualValuation)) :
    PolyIsoActionZp (actualZpLogShellFamily I j) where
  labelPerm := Fin.revPerm
  shellEquiv := fun i vQ v => zpSignShell I vQ v (ε i vQ)

theorem signActionZp_mem (j : Nat)
    (ε : SignChoice j (S1270NontrivialCapsuleActual.ActualValuation)) :
    signActionZp I j ε ∈ paperFullPolyIsoZp I j := by
  refine ⟨rfl, ε, ?_⟩
  intro i vQ v
  rfl

/-- The actual Z_p action of S1318 is the all--1 representative. -/
theorem actualZpPolyIso_mem (j : Nat) :
    actualZpPolyIso I j ∈ paperFullPolyIsoZp I j := by
  refine ⟨rfl, fun _ _ => true, ?_⟩
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
