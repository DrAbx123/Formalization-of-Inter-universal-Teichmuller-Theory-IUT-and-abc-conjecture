import tmp.sheaf.n8.closure.C9A1A2A3Source
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-!
# Source-reduct-preserving model test for C1

This is a research probe, not a production source construction.  The source
reduct is the actual `Theorem311Source.Input` together with the actual A1/A2/A3
records.  The extension adds only the symbols that the exact C1 attainment
statement needs: an output carrier, an allowed-output predicate, a q-pilot
point, a log-volume readout, and an IPL-like link relation.

The two extensions have the same source reduct and satisfy the same link and
upper-bound conditions.  One has a possible output with the q-log readout and
the other does not.  Thus the source signature plus the link/upper-bound
fragment cannot entail C1.  This does not claim a complete IUT countermodel:
the missing extension is precisely the source-level output-family/evaluation
construction under audit.
-/

noncomputable section
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.N8Closure.C9FullSignatureModel

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.C9A1A2A3Source

universe u v

variable {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## The fixed source reduct -/

structure SourceReduct (I : Theorem311Source.Input Label Choice) where
  a1 : Theorem311Source.Theorem311Output I
  a2 : A2 I
  a3 : A3 I

def actualSourceReduct (I : Theorem311Source.Input Label Choice) :
    SourceReduct I where
  a1 := A1 I
  a2 := A2.ofInput I
  a3 := A3.ofInput I

/-! ## The exact extra vocabulary needed for C1 -/

structure C1Extension (I : Theorem311Source.Input Label Choice)
    (S : SourceReduct I) where
  Output : Type
  QPilot : Type
  possible : Set Output
  qPilot : QPilot
  logVol : Output → Real
  qLog : Real
  hull : Real
  /-- The IPL fragment records a link but no readout equality. -/
  link : Output → QPilot → Prop
  output_nonempty : possible.Nonempty
  linked : ∀ d, d ∈ possible → link d qPilot
  hull_upper : ∀ d, d ∈ possible → logVol d ≤ hull

def exactAttainment
    {I : Theorem311Source.Input Label Choice}
    {S : SourceReduct I}
    (M : C1Extension I S) : Prop :=
  ∃ d, d ∈ M.possible ∧ M.logVol d = M.qLog

/-! ## Common data and the two expansions -/

def common (I : Theorem311Source.Input Label Choice)
    (S : SourceReduct I) : C1Extension I S where
  Output := Bool
  QPilot := Unit
  possible := {false}
  qPilot := ()
  logVol := fun b => if b then 1 else 0
  qLog := 1
  hull := 1
  link := fun _ _ => True
  output_nonempty := by
    exact ⟨false, by simp⟩
  linked := by
    intro d hd
    trivial
  hull_upper := by
    intro d hd
    have hd' : d = false := by simpa using hd
    subst d
    norm_num

def bad (I : Theorem311Source.Input Label Choice)
    (S : SourceReduct I) : C1Extension I S :=
  common I S

def good (I : Theorem311Source.Input Label Choice)
    (S : SourceReduct I) : C1Extension I S where
  Output := Bool
  QPilot := Unit
  possible := Set.univ
  qPilot := ()
  logVol := fun b => if b then 1 else 0
  qLog := 1
  hull := 1
  link := fun _ _ => True
  output_nonempty := ⟨false, Set.mem_univ _⟩
  linked := by intro d hd; trivial
  hull_upper := by
    intro d hd
    by_cases h : d
    · simp [h]
    · simp [h]

theorem same_source_reduct (I : Theorem311Source.Input Label Choice) :
    actualSourceReduct I = actualSourceReduct I := rfl

theorem bad_satisfies_source_and_link (I : Theorem311Source.Input Label Choice) :
    (bad I (actualSourceReduct I)).possible.Nonempty ∧
      (∀ d, d ∈ (bad I (actualSourceReduct I)).possible →
        (bad I (actualSourceReduct I)).link d
          (bad I (actualSourceReduct I)).qPilot) ∧
      (∀ d, d ∈ (bad I (actualSourceReduct I)).possible →
        (bad I (actualSourceReduct I)).logVol d ≤
          (bad I (actualSourceReduct I)).hull) := by
  exact ⟨(bad I (actualSourceReduct I)).output_nonempty,
    (bad I (actualSourceReduct I)).linked,
    (bad I (actualSourceReduct I)).hull_upper⟩

theorem good_satisfies_source_and_link (I : Theorem311Source.Input Label Choice) :
    (good I (actualSourceReduct I)).possible.Nonempty ∧
      (∀ d, d ∈ (good I (actualSourceReduct I)).possible →
        (good I (actualSourceReduct I)).link d
          (good I (actualSourceReduct I)).qPilot) ∧
      (∀ d, d ∈ (good I (actualSourceReduct I)).possible →
        (good I (actualSourceReduct I)).logVol d ≤
          (good I (actualSourceReduct I)).hull) := by
  exact ⟨(good I (actualSourceReduct I)).output_nonempty,
    (good I (actualSourceReduct I)).linked,
    (good I (actualSourceReduct I)).hull_upper⟩

theorem bad_not_exactAttainment (I : Theorem311Source.Input Label Choice) :
    ¬ exactAttainment (bad I (actualSourceReduct I)) := by
  intro h
  rcases h with ⟨d, hd, hv⟩
  have hd' : d = false := by simpa using hd
  subst d
  norm_num at hv

theorem good_exactAttainment (I : Theorem311Source.Input Label Choice) :
    exactAttainment (good I (actualSourceReduct I)) := by
  refine ⟨true, Set.mem_univ _, ?_⟩
  rfl

/-! The same source-side A1/A2/A3 facts are available in both expansions. -/

theorem source_A1_A2_A3_fixed (I : Theorem311Source.Input Label Choice) :
    (actualSourceReduct I).a1 = A1 I ∧
      Nonempty (A2 I) ∧ Nonempty (A3 I) := by
  exact ⟨rfl, ⟨(actualSourceReduct I).a2, (actualSourceReduct I).a3⟩⟩

end LeanFormal.IUT.N8Closure.C9FullSignatureModel

