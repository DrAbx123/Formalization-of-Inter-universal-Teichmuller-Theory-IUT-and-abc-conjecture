import tmp.sheaf.n8.closure.EtaIntegersZpModuleActual
import tmp.sheaf.n8.closure.EtaNNHullVolumeEqualityActual
import tmp.sheaf.n8.closure.EtaTensorStandardBorelActual

/-!
# EtaLvSubmoduleSetActual

Set identities for the actual Zp-submodules: `qSubmodule` is the image of
`Integers` under multiplication by `g^k` (`qORegion`), and `LvSubmodule` has
carrier `nnLattice`.  Consequently `LvSubmodule` is its own span.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaLvSubmoduleSetActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.EtaTensorStandardBorelActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismInterfaceActual
open LeanFormal.IUT.N8Closure.EtaTensorHullMeasureActual
open LeanFormal.IUT.N8Closure.EtaNnLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaNNOrbitHullBoundActual
open LeanFormal.IUT.N8Closure.EtaOrbitNonnegativeBounded
open LeanFormal.IUT.N8Closure.EtaNNHullVolumeActual
open LeanFormal.IUT.N8Closure.EtaNNHullVolumeEqualityActual
open LeanFormal.IUT.N8Closure.EtaIntegersZpModuleActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)
abbrev Zp : Type := ℤ_[nativePrime X]
abbrev g0 : Kf X := gNonIntegral X

local instance : Module (Zp X) (Kf X) :=
  Module.compHom (Kf X) (algebraMap (Zp X) (ℚ_[nativePrime X]))

local instance : Module (Zp X) (E X) :=
  Module.compHom (E X) (algebraMap (Zp X) (ℚ_[nativePrime X]))

theorem qSubmodule_coe (g : Kf X) (k : ℕ) :
    (qSubmodule X g k : Set (Kf X)) = qORegion X (g ^ k) := by
  ext x
  constructor
  · intro hx
    change x ∈ Submodule.map (mulZp X (g ^ k)) (integersSubmodule X) at hx
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, by simp [mulZp]⟩
  · intro hx
    rcases hx with ⟨o, -, hxo⟩
    rw [← hxo]
    change (g ^ k * (o : Kf X)) ∈
      Submodule.map (mulZp X (g ^ k)) (integersSubmodule X)
    rw [Submodule.mem_map]
    exact ⟨(o : Kf X), o.property, by simp [mulZp]⟩

theorem LvSubmodule_coe (g : Kf X) (k : ℕ) :
    (LvSubmodule X g k : Set (E X)) = nnLattice X g k := by
  ext x
  change x ∈ Submodule.map (tauSymmZp X) (qSubmodule X g k) ↔ x ∈ nnLattice X g k
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [nnLattice_eq_image]
    have hy' : y ∈ qORegion X (g ^ k) := by
      rw [show qORegion X (g ^ k) = (qSubmodule X g k : Set (Kf X)) from
        (qSubmodule_coe X g k).symm]
      exact hy
    exact ⟨y, hy', rfl⟩
  · rw [nnLattice_eq_image]
    rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ (qSubmodule X g k : Set (Kf X)) := by
      rw [qSubmodule_coe X g k]
      exact hy
    exact ⟨y, hy', rfl⟩

theorem nnLattice_mono_le_g0 {n m : ℕ} (h : n ≤ m) :
    nnLattice X (g0 X) n ⊆ nnLattice X (g0 X) m := by
  induction m, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ m hnm ih => exact ih.trans (nnLattice_mono_g0 X m)

theorem nnOrbitSubFinite_le_LvSubmodule (k : ℕ) :
    nnOrbitSubFinite X (g0 X) k ≤ LvSubmodule X (g0 X) k := by
  rw [nnOrbitSubFinite]
  apply Submodule.span_le.mpr
  rintro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  rw [LvSubmodule_coe]
  exact nnLattice_mono_le_g0 X (Nat.le_of_lt_succ n.isLt) hn

theorem LvSubmodule_le_nnOrbitSubFinite (k : ℕ) :
    LvSubmodule X (g0 X) k ≤ nnOrbitSubFinite X (g0 X) k := by
  intro x hx
  have hx' : x ∈ nnLattice X (g0 X) k := by
    rw [← LvSubmodule_coe X (g0 X) k]
    exact hx
  rw [nnOrbitSubFinite]
  exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_self k⟩, hx'⟩)

theorem nnOrbitSubFinite_eq_LvSubmodule (k : ℕ) :
    nnOrbitSubFinite X (g0 X) k = LvSubmodule X (g0 X) k :=
  le_antisymm (nnOrbitSubFinite_le_LvSubmodule X k) (LvSubmodule_le_nnOrbitSubFinite X k)

theorem span_LvSubmodule (g : Kf X) (k : ℕ) :
    Submodule.span (ℤ_[nativePrime X]) (LvSubmodule X g k : Set (E X)) =
      LvSubmodule X g k :=
  Submodule.span_eq (LvSubmodule X g k)

local instance : MeasurableSpace (E X) :=
  MeasurableSpace.map (tau X).symm (inferInstance : MeasurableSpace (Kf X))

theorem nnHullVolumeEqualityG0_actual (k : ℕ) :
    tensorHaar X (nnOrbitSubFinite X (g0 X) k) =
      ENNReal.ofReal ((‖(g0 X)‖ ^ k) ^
        (Module.finrank ℚ_[nativePrime X] (Kf X))) *
        (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X)) := by
  rw [nnOrbitSubFinite_eq_LvSubmodule, LvSubmodule_coe]
  exact tensorHaar_nnLattice_formula_actual X (g0 X) (gNonIntegral_ne_zero X) k

end LeanFormal.IUT.N8Closure.EtaLvSubmoduleSetActual