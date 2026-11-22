import Mathlib

import tmp.sheaf.xif.paper.Hull02ClosureOperatorActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# STEP 0 prior-art: Phi(P)|Xi(P)|indeterminacy|log-volume|Rem 3.9.5(iii)(iv) -> hits Hull01/02 (hull/closure laws), CardHullRealGeometryGapCards:62 (lambda.O scaling classes), S3132 V-form scaling RootedScalingDecomposition/log-volume monotonicity (arithmeticTupleNormalizedLogVolume_mono) -> ADAPT (abstract Phi/Xi layer; no re-proof of concrete log-volume facts).

# [Hull] 03: Phi/Xi hull-approximation sets and indeterminacy (Rem 3.9.5(iii)-(iv)) - class A abstract

Corpus: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt,
Remark 3.9.5(iii)-(iv): for a region P one considers
  Phi(P) = { H | H subset phi(P), mu_log(H) >= mu_log(P) },
  Xi(P)  = { H | H subset phi(P), mu_log(H) =  mu_log(P) },
the hull-approximant sets; phi(P) in Phi(P); Xi-non1 (nonemptiness condition) and
compactness of indeterminacy: all possible choices lie in phi(P).  This file defines
the abstract Phi/Xi sets over a hull system with a monotone log-volume functional
and proves: phi(P) in Phi(P), union of Phi(P) = phi(P), Xi(P) subset Phi(P),
Xi(P) nonempty (H := P), and phi(P) in Xi(P) exactly when the log-volume of P
equals that of its hull (the abstract Xi-non1 condition).  Class A; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Hull03PhiXiActual

open LeanFormal.IUT.XiFPaper.Hull01DefinitionActual
open LeanFormal.IUT.XiFPaper.Hull02ClosureOperatorActual

universe u

variable {X : Type u} (HS : HullSystem X)
variable (vol : Set X → ℝ)

/-- Monotonicity hypothesis for the log-volume functional (paper: log-volume is
monotone under inclusion). -/
def VolMonotone : Prop := ∀ {A B : Set X}, A ⊆ B → vol A ≤ vol B

/-- Phi(P): hull-approximants with log-volume at least that of P. -/
def Phi (hmono : VolMonotone vol) (P : Set X) : Set (Set X) :=
  {H | H ⊆ phi HS P ∧ vol P ≤ vol H}

/-- Xi(P): hull-approximants with log-volume exactly that of P. -/
def Xi (hmono : VolMonotone vol) (P : Set X) : Set (Set X) :=
  {H | H ⊆ phi HS P ∧ vol H = vol P}

/-- **phi(P) belongs to Phi(P)** (compactness of indeterminacy: the hull itself is
always a possible choice). -/
theorem phi_mem_Phi (hmono : VolMonotone vol) (P : Set X) :
    phi HS P ∈ Phi HS vol hmono P :=
  ⟨Set.Subset.refl _, hmono (phi_extensive HS P)⟩

/-- Every element of Phi(P) is contained in phi(P). -/
theorem Phi_subset (hmono : VolMonotone vol) (P : Set X) {H : Set X}
    (hH : H ∈ Phi HS vol hmono P) : H ⊆ phi HS P :=
  hH.1

/-- Xi(P) is contained in Phi(P). -/
theorem Xi_subset_Phi (hmono : VolMonotone vol) (P : Set X) :
    Xi HS vol hmono P ⊆ Phi HS vol hmono P := by
  intro H hH
  exact ⟨hH.1, le_of_eq hH.2.symm⟩

/-- **Xi(P) is nonempty** (abstract Xi-non1): the region P itself is an
approximant with equal log-volume. -/
theorem Xi_nonempty (hmono : VolMonotone vol) (P : Set X) :
    (Xi HS vol hmono P).Nonempty :=
  ⟨P, phi_extensive HS P, rfl⟩

/-- **Union of the hull-approximant set is the hull** (all possible choices lie in
phi(P), and phi(P) is itself a choice). -/
theorem sUnion_Phi (hmono : VolMonotone vol) (P : Set X) :
    ⋃₀ Phi HS vol hmono P = phi HS P := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_sUnion.mp hx with ⟨H, hH, hxH⟩
    exact hH.1 hxH
  · intro x hx
    exact Set.mem_sUnion.mpr ⟨phi HS P, phi_mem_Phi HS vol hmono P, hx⟩

/-- **Xi contains the hull exactly when the hull has no log-volume increase**
(the precise abstract form of the paper's Xi-non1 condition). -/
theorem phi_mem_Xi_iff (hmono : VolMonotone vol) (P : Set X) :
    phi HS P ∈ Xi HS vol hmono P ↔ vol (phi HS P) = vol P :=
  ⟨fun h => h.2, fun h => ⟨Set.Subset.refl _, h⟩⟩

#check VolMonotone
#check Phi
#check Xi
#check phi_mem_Phi
#check Xi_subset_Phi
#check Xi_nonempty
#check sUnion_Phi
#check phi_mem_Xi_iff

end LeanFormal.IUT.XiFPaper.Hull03PhiXiActual