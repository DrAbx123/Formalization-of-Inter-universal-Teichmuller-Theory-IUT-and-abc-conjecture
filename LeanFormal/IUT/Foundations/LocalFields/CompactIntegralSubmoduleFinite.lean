import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Compact integral submodules inside a space with an open finite lattice

A finite translate cover places every compact submodule inside the sum of
one open finite submodule and finitely many elements. Noetherianity then
proves finite generation. The actual p-adic open lattice is constructed
separately before applying this result to log-shells.
-/

namespace LeanFormal.IUT.CompactIntegralSubmodule

noncomputable section

variable {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
variable [TopologicalSpace M] [IsTopologicalAddGroup M]

omit [IsNoetherianRing R] in
theorem exists_fg_envelope_of_isCompact_of_open_fg (S : Set M) (N : Submodule R M)
    (hS : IsCompact S) (hN : IsOpen (N : Set M)) (hNfg : N.FG) :
    ∃ envelope : Submodule R M, envelope.FG ∧ S ⊆ envelope := by
  classical
  have hinterior : (interior (N : Set M)).Nonempty := by
    rw [hN.interior_eq]
    exact ⟨0, N.zero_mem⟩
  obtain ⟨centers, hcover⟩ := compact_covered_by_add_left_translates hS hinterior
  let envelope := N ⊔ Submodule.span R (centers : Set M)
  have hfg : envelope.FG := hNfg.sup (Submodule.fg_span centers.finite_toSet)
  have hsubset : S ⊆ envelope := by
    intro x hx
    change x ∈ envelope
    obtain ⟨center, hcenter⟩ := Set.mem_iUnion.mp (hcover hx)
    obtain ⟨hmem, htranslate⟩ := Set.mem_iUnion.mp hcenter
    have hsum : center + x ∈ envelope :=
      (show N ≤ envelope from le_sup_left) htranslate
    have hcenterMem : center ∈ envelope :=
      (show Submodule.span R (centers : Set M) ≤ envelope from le_sup_right)
        (Submodule.subset_span hmem)
    simpa only [add_sub_cancel_left] using envelope.sub_mem hsum hcenterMem
  exact ⟨envelope, hfg, hsubset⟩

theorem finite_of_isCompact_of_open_fg (S N : Submodule R M)
    (hS : IsCompact (S : Set M)) (hN : IsOpen (N : Set M)) (hNfg : N.FG) :
    Module.Finite R S := by
  obtain ⟨envelope, hfg, hinclusion⟩ :=
    exists_fg_envelope_of_isCompact_of_open_fg (S : Set M) N hS hN hNfg
  letI : Module.Finite R envelope := Module.Finite.iff_fg.mpr hfg
  exact Module.Finite.of_injective (Submodule.inclusion hinclusion) (by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : envelope => (z : M)) h)

theorem finite_span_of_isCompact_of_open_fg (S : Set M) (N : Submodule R M)
    (hS : IsCompact S) (hN : IsOpen (N : Set M)) (hNfg : N.FG) :
    Module.Finite R (Submodule.span R S) := by
  obtain ⟨envelope, hfg, hsubset⟩ :=
    exists_fg_envelope_of_isCompact_of_open_fg S N hS hN hNfg
  letI : Module.Finite R envelope := Module.Finite.iff_fg.mpr hfg
  exact Module.Finite.of_injective (Submodule.inclusion (Submodule.span_le.mpr hsubset)) (by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : envelope => (z : M)) h)

end

end LeanFormal.IUT.CompactIntegralSubmodule
