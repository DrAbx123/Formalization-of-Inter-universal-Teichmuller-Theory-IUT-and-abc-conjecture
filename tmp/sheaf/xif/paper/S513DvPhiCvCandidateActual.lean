import tmp.sheaf.xif.paper.S508PaperPhiCvCandidateActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S513DvPhiCvCandidateActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S508PaperPhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.SourceFinitePlaceReconstruction
open Iut.SourceModelFrobenioid

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev DvPhiBase : Type := Example32SmallBase T.arithmetic.K

/-- The K-side q_v order section: qOrder = N * (qVFamilyK T b).order. -/
noncomputable def dvQOrderSection (N : ℕ) (hN : 0 < N) :
    DvSmallQOrderSection (K := T.arithmetic.K) where
  qOrder := N * (qVFamilyK T b).order
  qOrder_pos := Nat.mul_pos hN (qVFamilyK T b).order_pos

/-- The N * qOrder submonoid of the stage divisor monoid. -/
noncomputable def dvSplitSubmonoid (N : ℕ) (hN : 0 < N) :
    Submonoid (StageDivisor.{u+1}) :=
  nsmulQOrderSubmonoid (K := T.arithmetic.K) (dvQOrderSection T b N hN)

theorem dvQOrder_mem_split (N : ℕ) (hN : 0 < N) :
    (N * (qVFamilyK T b).order) • (1 : StageDivisor.{u+1}) ∈
      dvSplitSubmonoid (T := T) (b := b) N hN := by
  unfold dvSplitSubmonoid nsmulQOrderSubmonoid dvQOrderSection
  refine ⟨1, ?_⟩
  simp

/-- Candidate Dv-side Phi_Cv: conditional on an explicit ramification-index
interface, with q_v order from qVFamilyK. -/
structure DvPhiCvCandidate (N : ℕ) (hN : 0 < N) where
  ramification : DvSmallRamificationIndexData (K := T.arithmetic.K)
  phi : DivisorialMonoidOn (Example32SmallBase T.arithmetic.K)
    (fun {_ _} f => IsIso f)
  phi_eq : phi = paperPhiCvCandidate (K := T.arithmetic.K) ramification
  qOrderSection : DvSmallQOrderSection (K := T.arithmetic.K)
  qOrder_eq : qOrderSection.qOrder = N * (qVFamilyK T b).order
  split : Submonoid (StageDivisor.{u+1})
  split_eq : split = nsmulQOrderSubmonoid (K := T.arithmetic.K) qOrderSection
  qOrder_mem_split :
    qOrderSection.qOrder • (1 : StageDivisor.{u+1}) ∈ split

noncomputable def dvPhiCvCandidate
    (N : ℕ) (hN : 0 < N)
    (E : DvSmallRamificationIndexData (K := T.arithmetic.K)) :
    DvPhiCvCandidate (T := T) (b := b) N hN where
  ramification := E
  phi := paperPhiCvCandidate (K := T.arithmetic.K) E
  phi_eq := rfl
  qOrderSection := dvQOrderSection T b N hN
  qOrder_eq := rfl
  split := dvSplitSubmonoid T b N hN
  split_eq := rfl
  qOrder_mem_split := dvQOrder_mem_split T b N hN

/-- Exact missing Dv base/ramification interface. -/
def DvPhiCvCandidateRequired : Prop :=
  Nonempty (DvSmallRamificationIndexData (K := T.arithmetic.K))

end LeanFormal.IUT.XiFPaper.S513DvPhiCvCandidateActual

end
