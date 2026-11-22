import tmp.sheaf.n8.closure.EtaNNHullSubmoduleActual

/-!
# EtaIntegersZpModuleActual

Explicit `Module ℤ_[p] (Integers Kf)` via the ring hom `ℤ_[p] → Integers Kf`
(the `ℤ_[p] → ℚ_[p] → Kf` image has norm ≤1), and the resulting integers
`ℤ_[p]`-submodule.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaIntegersZpModuleActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaNNHullVolumeEqualityActual
open LeanFormal.IUT.N8Closure.EtaOrbitNonnegativeBounded
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaNNHullSubmoduleActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)
abbrev Zp : Type := ℤ_[nativePrime X]

local instance : Module (Zp X) (Kf X) :=
  Module.compHom (Kf X) (algebraMap (Zp X) (ℚ_[nativePrime X]))

noncomputable def zpEmbed (a : Zp X) : Kf X :=
  algebraMap (ℚ_[nativePrime X]) (Kf X)
    (algebraMap (Zp X) (ℚ_[nativePrime X]) a)

theorem norm_zpEmbed_le_one (a : Zp X) : ‖zpEmbed X a‖ ≤ 1 := by
  have ha : ‖a‖ ≤ 1 := PadicInt.norm_le_one a
  simpa [zpEmbed, norm_algebraMap'] using ha

noncomputable def zpToIntegers : Zp X →+* Integers (Kf X) where
  toFun a := ⟨zpEmbed X a, by
    rw [LocalFieldIntegralUnits.mem_integers_iff]
    exact norm_zpEmbed_le_one X a⟩
  map_zero' := Subtype.ext (by simp [zpEmbed])
  map_one' := Subtype.ext (by simp [zpEmbed])
  map_add' a b := Subtype.ext (by simp [zpEmbed, map_add])
  map_mul' a b := Subtype.ext (by simp [zpEmbed, map_mul])

local instance : Module (Zp X) (Integers (Kf X)) :=
  Module.compHom (Integers (Kf X)) (zpToIntegers X)

noncomputable def integersSubmodule : Submodule (Zp X) (Kf X) where
  carrier := (Integers (Kf X) : Set (Kf X))
  zero_mem' := (Integers (Kf X)).zero_mem
  add_mem' := fun hx hy => (Integers (Kf X)).add_mem hx hy
  smul_mem' := by
    intro a x hx
    refine (LocalFieldIntegralUnits.mem_integers_iff (K := Kf X) (a • x)).mpr ?_
    have hx' : ‖x‖ ≤ 1 :=
      (LocalFieldIntegralUnits.mem_integers_iff (K := Kf X) x).mp hx
    have hsmul : a • x = zpEmbed X a * x := by
      rw [zpEmbed]
      change (algebraMap (Zp X) (ℚ_[nativePrime X]) a) • x =
        (algebraMap (ℚ_[nativePrime X]) (Kf X))
          (algebraMap (Zp X) (ℚ_[nativePrime X]) a) * x
      rw [Algebra.smul_def]
    rw [hsmul, norm_mul]
    exact mul_le_one₀ (norm_zpEmbed_le_one X a) (norm_nonneg _) hx'

local instance : Module (Zp X) (E X) :=
  Module.compHom (E X) (algebraMap (Zp X) (ℚ_[nativePrime X]))

noncomputable def tauZp : E X →ₗ[Zp X] (Kf X) where
  toFun := tau X
  map_add' := (tau X).map_add
  map_smul' := by
    intro a x
    change tau X ((algebraMap (Zp X) (ℚ_[nativePrime X]) a) • x) =
      (algebraMap (Zp X) (ℚ_[nativePrime X]) a) • tau X x
    exact (tau X).map_smul _ x

noncomputable def tauSymmZp : Kf X →ₗ[Zp X] (E X) where
  toFun := (tau X).symm
  map_add' := (tau X).symm.map_add
  map_smul' := by
    intro a x
    change (tau X).symm ((algebraMap (Zp X) (ℚ_[nativePrime X]) a) • x) =
      (algebraMap (Zp X) (ℚ_[nativePrime X]) a) • (tau X).symm x
    exact (tau X).symm.map_smul _ x

noncomputable def mulZp (g : Kf X) : Kf X →ₗ[Zp X] (Kf X) where
  toFun x := g * x
  map_add' := fun x y => mul_add g x y
  map_smul' := by
    intro a x
    change g * ((algebraMap (Zp X) (ℚ_[nativePrime X]) a) • x) =
      (algebraMap (Zp X) (ℚ_[nativePrime X]) a) • (g * x)
    rw [Algebra.smul_def, Algebra.smul_def]
    ring

noncomputable def qSubmodule (g : Kf X) (k : ℕ) : Submodule (Zp X) (Kf X) :=
  Submodule.map (mulZp X (g ^ k)) (integersSubmodule X)

noncomputable def LvSubmodule (g : Kf X) (k : ℕ) : Submodule (Zp X) (E X) :=
  Submodule.map (tauSymmZp X) (qSubmodule X g k)

def MissingLvSubmoduleSet (X : N8NativeInput l) : Prop :=
  ∀ (g : Kf X) (k : ℕ),
    (LvSubmodule X g k : Set (E X)) = nnLattice X g k

end LeanFormal.IUT.N8Closure.EtaIntegersZpModuleActual