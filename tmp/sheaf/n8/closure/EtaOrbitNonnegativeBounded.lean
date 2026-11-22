import tmp.sheaf.n8.closure.EtaTensorGraphOrbitSaturation
import tmp.sheaf.n8.closure.EtaOrbitFiniteLevelKN

/-!
# EtaOrbitNonnegativeBounded

Target correction: use only nonnegative powers `g^n` (`n : ℕ`), avoiding the
unbounded negative-power orbit.  Actual finite-range orbit spans, inclusions
into the full nonnegative orbit span, and forward edge bounds are proved.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaOrbitNonnegativeBounded

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaTensorSplitActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphCertificateActual
open LeanFormal.IUT.N8Closure.EtaTensorZpSubmoduleLatticeActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphOrbitSaturation
open LeanFormal.IUT.N8Closure.EtaOrbitSaturationEqualityActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismInterfaceActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.FiniteObservationHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)
abbrev g0 : Kf X := gNonIntegral X

local instance : Module (ℤ_[nativePrime X]) (E X) :=
  Module.compHom (E X) (algebraMap (ℤ_[nativePrime X]) (ℚ_[nativePrime X]))

noncomputable def nnLattice (g : Kf X) (n : ℕ) : Set (E X) :=
  Lv X (g ^ n)

noncomputable def nnOrbitSet (g : Kf X) : Set (E X) :=
  ⋃ n : ℕ, nnLattice X g n

noncomputable def nnOrbitSub (g : Kf X) : Submodule (ℤ_[nativePrime X]) (E X) :=
  Submodule.span (ℤ_[nativePrime X]) (nnOrbitSet X g)

noncomputable def nnOrbitFinite (g : Kf X) (k : ℕ) : Set (E X) :=
  ⋃ n : Fin (k + 1), nnLattice X g n

noncomputable def nnOrbitSubFinite (g : Kf X) (k : ℕ) :
    Submodule (ℤ_[nativePrime X]) (E X) :=
  Submodule.span (ℤ_[nativePrime X]) (nnOrbitFinite X g k)

theorem nnFinite_le_full (g : Kf X) (k : ℕ) :
    nnOrbitSubFinite X g k ≤ nnOrbitSub X g := by
  rw [nnOrbitSubFinite, nnOrbitSub]
  apply Submodule.span_mono
  rintro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n.1, hn⟩

theorem nnTensorEdge (g : Kf X) (n : ℕ) :
    GraphEdge X g (nnLattice X g n) (nnLattice X g (n + 1)) := by
  rintro y ⟨o, rfl⟩
  have hxmem : (PiTensorProduct.tprod (ℚ_[nativePrime X])
      (fun _ : Unit => g ^ n * (o : Kf X))) ∈ Lv X (g ^ n) :=
    ⟨o, rfl⟩
  have h := (tensorEdge_scaled X (g ^ n) g)
    (PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => g ^ n * (o : Kf X)))
    hxmem
  convert h using 2
  change Lv X (g ^ (n + 1)) = Lv X (g * g ^ n)
  congr 1
  rw [pow_succ']

theorem nnEdgeZp_maps_finite (g : Kf X) (hg : g ≠ 0) (k : ℕ) :
    Submodule.map (EtaTensorGraphOrbitSaturation.edgeZp X g hg)
      (nnOrbitSubFinite X g k) ≤ nnOrbitSubFinite X g (k + 1) := by
  rw [nnOrbitSubFinite, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  have hmem : graphAction X g x ∈ nnLattice X g (n + 1) :=
    (nnTensorEdge X g n) x hn
  have hx' : (graphEquiv X g hg) x = graphAction X g x :=
    DFunLike.congr_fun (graphEquiv_coe_actual X g hg) x
  change (graphEquiv X g hg) x ∈ Submodule.span (ℤ_[nativePrime X]) (nnOrbitFinite X g (k + 1))
  rw [hx']
  refine Submodule.subset_span (Set.mem_iUnion.mpr ⟨n.succ, ?_⟩)
  exact hmem

theorem nnEdgeZp_maps_full (g : Kf X) (hg : g ≠ 0) :
    Submodule.map (EtaTensorGraphOrbitSaturation.edgeZp X g hg)
      (nnOrbitSub X g) ≤ nnOrbitSub X g := by
  rw [nnOrbitSub, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  have hmem : graphAction X g x ∈ nnLattice X g (n + 1) :=
    (nnTensorEdge X g n) x hn
  have hx' : (graphEquiv X g hg) x = graphAction X g x :=
    DFunLike.congr_fun (graphEquiv_coe_actual X g hg) x
  change (graphEquiv X g hg) x ∈ Submodule.span (ℤ_[nativePrime X]) (nnOrbitSet X g)
  rw [hx']
  exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨n + 1, hmem⟩)

theorem nnInnerOuterBound (g : Kf X) (k : ℕ) :
    nnOrbitSubFinite X g k ≤ nnOrbitSub X g := nnFinite_le_full X g k

end LeanFormal.IUT.N8Closure.EtaOrbitNonnegativeBounded