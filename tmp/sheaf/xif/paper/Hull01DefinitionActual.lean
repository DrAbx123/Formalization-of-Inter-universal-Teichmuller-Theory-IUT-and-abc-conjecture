import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: holomorphic hull|actualHolomorphicHull|actualCandidateHulls|actualScaledRegion|hull operator|Rem 3.9.5 -> hits tmp/sheaf/xif/paper/C3LogShellTensorHolomorphicHullActual.lean:54/58/62/68/76/82/93 (actualUnitRegion/actualNonzeroScalings/actualScaledRegion/actualCandidateHulls/actualHolomorphicHull + contains/least theorems), LeanFormal CardHullRealGeneratorNonpositivity:56 (cites Rem 3.9.5(i) 7652-7680), CardHullRealGeometryGapCards:62 -> REUSE/ADAPT (abstract hull-system layer; no re-proof of concrete C3 facts).

# [Hull] 01: hull definition and well-definedness (IUT III Rem 3.9.5(i)) - class A

Corpus: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt,
Remark 3.9.5(i) (corpus 7652-7680): the holomorphic hull of a region P is the
smallest subset of the form H = lambda*O (all components of lambda nonzero) that
contains P; if P is not relatively compact the hull is the whole IQ.
This file abstracts the definition: a HULL SYSTEM is a type X with a family of
scaled regions closed under arbitrary intersections; the hull is the intersection
of all family members containing P.  We prove: containment, leastness,
family-membership of the hull, and UNIQUENESS of a least scaled region containing
P (hence well-definedness of the paper's hull).  The concrete C3 instantiation
(actualScaledRegion/actualCandidateHulls/actualHolomorphicHull) is reused from
C3LogShellTensorHolomorphicHullActual and is an instance of this pattern.
Class A; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Hull01DefinitionActual

universe u

/-- A hull system: a type with a family of scaled regions (lambda*O) closed under
arbitrary intersections (the paper's holomorphic-hull family). -/
structure HullSystem (X : Type u) where
  /-- the family of scaled regions lambda*O (with all components of lambda nonzero) -/
  Family : Set (Set X)
  /-- arbitrary intersections of family members are again family members -/
  inter_mem : ∀ S : Set (Set X), (∀ H ∈ S, Family H) → Family (⋂₀ S)

namespace HullSystem

variable {X : Type u} (HS : HullSystem X)

/-- The holomorphic hull: intersection of all scaled regions containing P
(the abstract form of the paper's smallest lambda*O containing P). -/
def hull (P : Set X) : Set X :=
  ⋂₀ {H | HS.Family H ∧ P ⊆ H}

/-- The region is contained in its hull (Rem 3.9.5(i) containment). -/
theorem subset_hull (P : Set X) : P ⊆ HS.hull P := by
  intro x hx
  rw [hull]
  exact Set.mem_sInter.mpr (fun H hH => hH.2 hx)

/-- Leastness: the hull is contained in every scaled region containing P. -/
theorem hull_subset (P H : Set X) (hF : HS.Family H) (hP : P ⊆ H) :
    HS.hull P ⊆ H := by
  intro x hx
  rw [hull] at hx
  exact (Set.mem_sInter.mp hx) H ⟨hF, hP⟩

/-- The hull is itself a scaled region (family member). -/
theorem hull_mem_family (P : Set X) : HS.Family (HS.hull P) := by
  rw [hull]
  exact HS.inter_mem _ (fun H hH => hH.1)

/-- Monotonicity of the hull in the region. -/
theorem hull_mono {P Q : Set X} (h : P ⊆ Q) : HS.hull P ⊆ HS.hull Q := by
  intro x hx
  rw [hull] at hx ⊢
  exact Set.mem_sInter.mpr (fun H hH =>
    (Set.mem_sInter.mp hx) H ⟨hH.1, fun y hy => hH.2 (h hy)⟩)

/-- Idempotence of the hull. -/
theorem hull_idem (P : Set X) : HS.hull (HS.hull P) = HS.hull P := by
  apply Set.Subset.antisymm
  · exact hull_subset HS (HS.hull P) (HS.hull P) (hull_mem_family HS P)
      (Set.Subset.refl _)
  · exact hull_mono HS (subset_hull HS P)

/-- **Uniqueness of the least scaled region containing P** (well-definedness of
the paper's holomorphic hull). -/
theorem eq_of_least (P H : Set X) (hF : HS.Family H) (hP : P ⊆ H)
    (hleast : ∀ H' : Set X, HS.Family H' → P ⊆ H' → H ⊆ H') :
    HS.hull P = H := by
  apply Set.Subset.antisymm
  · exact hull_subset HS P H hF hP
  · exact hleast (HS.hull P) (hull_mem_family HS P) (subset_hull HS P)

#check HullSystem
#check HullSystem.hull
#check HullSystem.subset_hull
#check HullSystem.hull_subset
#check HullSystem.hull_mem_family
#check HullSystem.hull_mono
#check HullSystem.hull_idem
#check HullSystem.eq_of_least

end HullSystem

end LeanFormal.IUT.XiFPaper.Hull01DefinitionActual