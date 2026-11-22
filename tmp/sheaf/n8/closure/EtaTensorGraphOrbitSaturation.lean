import tmp.sheaf.n8.closure.EtaTensorZpSubmoduleLatticeActual

/-!
# EtaTensorGraphOrbitSaturation

Orbit lattices `L_n = g^n * Integers` and their `ℤ_[p]`-span.  The actual
tensor action maps `L_n` into `L_{n+1}`; hence the orbit span is saturated
under both `g` and `g⁻¹` (inclusion form).  The exact equality/fixed-point
step is recorded as a gap.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaTensorGraphOrbitSaturation

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaTensorSplitActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphCertificateActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismInterfaceActual
open LeanFormal.IUT.N8Closure.FiniteObservationHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

local instance : Module (ℤ_[nativePrime X]) (E X) :=
  Module.compHom (E X) (algebraMap (ℤ_[nativePrime X]) (ℚ_[nativePrime X]))

noncomputable def orbitLattice (g : Kf X) (n : ℤ) : Set (E X) :=
  Lv X (g ^ n)

noncomputable def orbitSet (g : Kf X) : Set (E X) :=
  ⋃ n : ℤ, orbitLattice X g n

noncomputable def orbitSub (g : Kf X) : Submodule (ℤ_[nativePrime X]) (E X) :=
  Submodule.span (ℤ_[nativePrime X]) (orbitSet X g)

theorem tensorEdge_scaled (a g : Kf X) :
    GraphEdge X g (Lv X a) (Lv X (g * a)) := by
  rintro y ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  change PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => g * a * (x : Kf X)) =
    graphAction X g (PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => a * (x : Kf X)))
  rw [graphAction, tensorActionMul, LinearMap.mulLeft_apply]
  change PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => g * a * (x : Kf X)) =
    PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => g) *
      PiTensorProduct.tprod (ℚ_[nativePrime X]) (fun _ : Unit => a * (x : Kf X))
  rw [PiTensorProduct.tprod_mul_tprod]
  congr 1
  funext i
  simp only [Pi.mul_apply]
  ring

noncomputable def edgeZp (g : Kf X) (hg : g ≠ 0) : E X →ₗ[ℤ_[nativePrime X]] E X where
  toFun := graphEquiv X g hg
  map_add' := (graphEquiv X g hg).map_add
  map_smul' := by
    intro a x
    change graphEquiv X g hg (a • x) = a • graphEquiv X g hg x
    rw [show a • x = (algebraMap (ℤ_[nativePrime X]) (ℚ_[nativePrime X]) a) • x from rfl]
    rw [show a • graphEquiv X g hg x =
      (algebraMap (ℤ_[nativePrime X]) (ℚ_[nativePrime X]) a) • graphEquiv X g hg x from rfl]
    exact (graphEquiv X g hg).map_smul _ x

theorem edgeZp_maps_orbit (g : Kf X) (hg : g ≠ 0) :
    Submodule.map (edgeZp X g hg) (orbitSub X g) ≤ orbitSub X g := by
  rw [orbitSub, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  have hmem : graphAction X g x ∈ Lv X (g * g ^ n) :=
    tensorEdge_scaled X (g ^ n) g x hn
  have hx' : (graphEquiv X g hg) x = graphAction X g x :=
    DFunLike.congr_fun (graphEquiv_coe_actual X g hg) x
  change (graphEquiv X g hg) x ∈ (Submodule.span ℤ_[nativePrime X] (orbitSet X g))
  rw [hx']
  refine Submodule.subset_span (Set.mem_iUnion.mpr ⟨n + 1, ?_⟩)
  show graphAction X g x ∈ Lv X (g ^ (n + 1))
  convert hmem using 2
  rw [zpow_add_one₀ hg]
  ring

theorem orbitHullCertificate_actual (g : Kf X) :
    InnerOuterHullCertificate (V := E X) (⊤ : Subring (ℤ_[nativePrime X]))
      (orbitSub X g) (orbitSub X g) (orbitSub X g) :=
  ⟨le_rfl, le_rfl, rfl⟩

theorem orbitHull_eq_actual (g : Kf X) :
    hull (⊤ : Subring (ℤ_[nativePrime X])) (orbitSub X g) =
      hull (⊤ : Subring (ℤ_[nativePrime X])) (orbitSub X g) :=
  inner_outer_hull_certificate (orbitSub X g) (orbitSub X g) (orbitSub X g)
    le_rfl le_rfl rfl

/-- Exact gap: the reverse inclusion/fixed-point equality for the actual orbit
span. -/
def OrbitSaturationEquality (g : Kf X) (hg : g ≠ 0) : Prop :=
  Submodule.map (edgeZp X g hg) (orbitSub X g) = orbitSub X g

end LeanFormal.IUT.N8Closure.EtaTensorGraphOrbitSaturation