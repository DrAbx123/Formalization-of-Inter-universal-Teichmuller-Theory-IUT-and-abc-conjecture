import tmp.sheaf.xif.paper.S432SmallModelActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-! # S511: independent Phi_Cv candidate with N-valued carrier and ramification pullback

This is a candidate interface: the carrier is `Nat` and the pullback is
multiplication by the ramification index.  It does not claim the
universe-lifted `DivisorialMonoidOn` instance, whose exact universe boundary
was recorded in S506.  The q_v generator and the N submonoid are included.
-/

namespace LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S432SmallModelActual

universe u
variable {K : Type u} [Field K]

/-- Ramification-index data for the small base. -/
structure RamificationIndexData where
  e : ∀ {X Y : Example32SmallBase K}, (X ⟶ Y) → ℕ+
  e_id : ∀ X : Example32SmallBase K, e (𝟙 X) = 1
  e_comp : ∀ {X Y Z : Example32SmallBase K} (f : X ⟶ Y) (g : Y ⟶ Z),
    e (f ≫ g) = e f * e g
  e_iso : ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), IsIso f → e f = 1

/-- N-valued carrier of the candidate Phi_Cv. -/
abbrev PhiCvCarrier (_X : Example32SmallBase K) : Type := ℕ

/-- Ramification pullback `n ↦ e(f) * n`. -/
noncomputable def phiCvPullback
    (R : RamificationIndexData (K := K)) {X Y : Example32SmallBase K}
    (f : X ⟶ Y) : PhiCvCarrier (K := K) Y →+ PhiCvCarrier (K := K) X where
  toFun n := (R.e f).val * n
  map_zero' := Nat.mul_zero _
  map_add' n m := Nat.mul_add _ _ _

theorem phiCvPullback_id
    (R : RamificationIndexData (K := K)) (X : Example32SmallBase K) :
    phiCvPullback (K := K) R (𝟙 X) = AddMonoidHom.id (PhiCvCarrier (K := K) X) := by
  apply AddMonoidHom.ext
  intro n
  simp [phiCvPullback, R.e_id]

theorem phiCvPullback_comp
    (R : RamificationIndexData (K := K))
    {X Y Z : Example32SmallBase K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    phiCvPullback (K := K) R (f ≫ g) =
      (phiCvPullback (K := K) R f).comp (phiCvPullback (K := K) R g) := by
  apply AddMonoidHom.ext
  intro n
  simp [phiCvPullback, R.e_comp, Nat.mul_assoc]

/-- Multiples of a coefficient: the `N · q_v` submonoid of `Nat`. -/
def nSubmonoid (N : ℕ) : AddSubmonoid ℕ where
  carrier := { n | ∃ k : ℕ, n = k * N }
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, by ring⟩

theorem nSubmonoid_mem_self (N : ℕ) : N ∈ nSubmonoid N := ⟨1, by simp⟩

/-- Candidate Phi_Cv package: actual ramification pullback, q_v generator,
and N submonoid. -/
structure PhiCvCandidate where
  ramification : RamificationIndexData (K := K)
  qvOrder : ℕ
  qvOrder_pos : 0 < qvOrder
  qvGenerator : ∀ X : Example32SmallBase K, PhiCvCarrier X := fun _ => qvOrder
  nSub : AddSubmonoid ℕ := nSubmonoid qvOrder
  qvGenerator_mem_nSub : ∀ X, qvGenerator X ∈ nSub

noncomputable def phiCvCandidateOf (R : RamificationIndexData (K := K))
    (N : ℕ) (hN : 0 < N) : PhiCvCandidate (K := K) where
  ramification := R
  qvOrder := N
  qvOrder_pos := hN
  qvGenerator := fun _ => N
  nSub := nSubmonoid N
  qvGenerator_mem_nSub := fun _ => nSubmonoid_mem_self N

end LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual

end
