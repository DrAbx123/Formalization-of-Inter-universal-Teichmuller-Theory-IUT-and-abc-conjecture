import tmp.sheaf.xif.paper.S432SmallModelActual
import Iut.Foundations.SourceModelFrobenioid
/-! # S508: paper Phi_Cv candidate interface on Example32SmallBase
D = Example32SmallBase K.  The paper candidate has obj X = N, pullback =
multiplication by the ramification index e(f), and a q_v section generating
N * qOrder.  The ramification-index laws are explicit input data; no index and
no valuation is faked.  The full DivisorialMonoidOn construction is recorded
as exact missing when the index data is absent. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S508PaperPhiCvCandidateActual
open CategoryTheory
open Iut
open Iut.SourceModelFrobenioid
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
universe u
variable (K : Type u) [Field K]
/-- Ramification-index interface for the q-side paper candidate. -/
structure DvSmallRamificationIndexData where
  index : ∀ {X Y : Example32SmallBase K}, (X ⟶ Y) → ℕ
  index_pos : ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), 0 < index f
  index_id : ∀ X : Example32SmallBase K, index (𝟙 X) = 1
  index_comp : ∀ {X Y Z : Example32SmallBase K} (f : X ⟶ Y) (g : Y ⟶ Z),
    index (f ≫ g) = index f * index g
  index_iso : ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), IsIso f → index f = 1
/-- A q_v section order (to be instantiated by qVFamilyK.order). -/
structure DvSmallQOrderSection where
  qOrder : ℕ
  qOrder_pos : 0 < qOrder
/-- The N * qOrder submonoid of N. -/
noncomputable def nsmulQOrderAddSubmonoid
    (Q : DvSmallQOrderSection) : AddSubmonoid ℕ where
  carrier := {n | ∃ k : ℕ, n = k * Q.qOrder}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ring
/-- Exact data package for the candidate. -/
structure PaperPhiCvCandidateData where
  ramification : DvSmallRamificationIndexData (K := K)
  qOrderSection : DvSmallQOrderSection
/-- Exact missing candidate data. -/
def PaperPhiCvCandidateRequired : Prop :=
  Nonempty (PaperPhiCvCandidateData (K := K))
/-- Exact missing full DivisorialMonoidOn with obj N and mulLeft ramification. -/
def PaperPhiCvDivisorialMonoidRequired : Prop :=
  Nonempty (DivisorialMonoidOn.{u+1} (Example32SmallBase K)
    (fun f => IsIso f))
end LeanFormal.IUT.XiFPaper.S508PaperPhiCvCandidateActual
