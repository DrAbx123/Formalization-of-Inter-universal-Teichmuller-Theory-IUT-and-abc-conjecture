import LeanFormal/IUT/IUTII/Kummer/SourceLogShellXMuPacket
import LeanFormal/IUT/IUTIII/Theorem311/SourceK1K2VolumeTranslationLaw
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullInterfaceDischarge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ConsumerVolumeXMuHullActual — A476 real consumer theorems (volume/XMu/hull)

New conclusions combining existing donor theorems:

* K1/K2 volume (\`SourceK1K2VolumeTranslationLaw.lean:79/90\`):
  \`volumeFiberFactorLaw_of_volumeTranslationData\` — translation data implies the
  fiber-factor (class) law by chaining the class-law theorem with the
  fiber-factor equivalence;
* XMu packet (\`SourceLogShellXMuPacket.lean:93/99/105\`):
  \`xMuPacket_mem_span_pi\` (decomposition + membership) and
  \`xMuPacket_single_fiber_package\` (single-fiber inclusion + per-fiber
  characterization jointly);
* hull representation (\`SourceHullInterfaceDischarge.lean:85\`):
  \`hull_representation_finite_package\` — the real representation, the lower
  bound transfer and the finiteness of the hull log-volume jointly.

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ConsumerVolumeXMuHullActual

open LeanFormal.IUT

/-- **Volume fiber-factor consumer**: volume-translation data implies the
fiber-factor law (class-law theorem + fiber-factor equivalence). -/
theorem volumeFiberFactorLaw_of_volumeTranslationData {ι : Type*}
    (volume : ι → Real) (F : Nat → ι → ι)
    (h : K1K2Realization.VolumeTranslationData volume F) :
    K1K2Realization.VolumeFiberFactorLaw volume F :=
  (K1K2Realization.volumeFiberFactorLaw_iff_volumeClassLaw volume F).mpr
    (K1K2Realization.volumeClassLaw_of_volumeTranslationData volume F h)

/-- **XMu packet membership/span chain consumer**. -/
theorem xMuPacket_mem_span_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → SourceLogShellDatum) (x : (i : ι) → (X i).K) :
    x ∈ sourceLogShellXMuPacket X ↔
      x ∈ Submodule.span ℚ (sourceLogShellDirectSumPacketSet X) := by
  rw [sourceLogShellXMuPacket_eq_span_pi X]

/-- **XMu single-fiber package consumer**: single-fiber inclusion and the
per-fiber characterization hold jointly. -/
theorem xMuPacket_single_fiber_package {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → SourceLogShellDatum) (i : ι) {x : (X i).K}
    (hx : x ∈ (X i).IQSpan) :
    (LinearMap.single ℚ (fun i => (X i).K) i x) ∈ sourceLogShellXMuPacket X ∧
      (∀ j, (LinearMap.single ℚ (fun i => (X i).K) i x) j ∈ (X j).IQSpan) :=
  ⟨sourceLogShellXMuPacket_single_mem X i hx,
   (sourceLogShellXMuPacket_mem_iff X _).mp
     (sourceLogShellXMuPacket_single_mem X i hx)⟩

/-- **Hull representation package consumer**: real representation, lower-bound
transfer and finiteness jointly. -/
theorem hull_representation_finite_package {X : Type*}
    (W : IQHullLogVolumeInterface X) {lowerBound : ENNReal}
    (h : lowerBound ≤ W.logVolume W.imageSet) :
    ∃ M : Real, W.logVolume W.hull = ENNReal.ofReal M ∧
      lowerBound ≤ ENNReal.ofReal M ∧ W.logVolume W.hull < ⊤ := by
  obtain ⟨M, hM, hle⟩ := IQHullLogVolumeInterface.hull_logVolume_realRepresentation W h
  exact ⟨M, hM, hle, W.hull_logVolume_lt_top⟩

#check volumeFiberFactorLaw_of_volumeTranslationData
#check hull_representation_finite_package

end LeanFormal.IUT.XiFPaper.Mzk1ConsumerVolumeXMuHullActual
end