import ContinuousKummerTheory.Kummer.Basic
import Reciprocity.Artin
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

/-!
# S3139: C2 paper-faithful conjugate copy action from the existing local CFT tools

This module REUSES the existing local class-field-theory port (lakefile.toml
libs Reciprocity / ContinuousKummerTheory) to assemble the paper-faithful
finite-place conjugate copy channel of the first triangle (IUT III:616-620,
Fig. I.5):

* `sourceLocalArtinMap`: the local Artin map
  PadicField.artin : K^x ->* Gal(K^ab/K)  (Reciprocity/Artin.lean:133);
* `sourceLocalKummerClass`: the local Kummer map
  KummerTheory.kummer : K^x ->* ContH1 Gal(Omega/K) (Mu n Omega)
  (ContinuousKummerTheory/Kummer/Basic.lean:215);
* `sourceKummerCopyEquiv`: the copy action on the local Kummer classes: the
  copy a acts by multiplication by its Kummer class (the Kummer map is
  multiplicative, so this is the actual translation action of the local unit
  group on the Kummer layer), with the unit and composition laws proved.

The remaining identification -- matching the Kummer class with the Artin
character (Galois-Kummer compatibility of the (Ind2) indeterminacy) -- is
recorded as the exact missing structure `SourceKummerArtinCompatibility` with
page refs, not assumed.

No sorry/axiom/True/PUnit/toy carrier.  **Component, not paper object.**
-/

namespace LeanFormal.IUT.XiFPaper.S3139C2LocalKummerCopyActual

open KummerTheory

universe uK uΩ

/-! ## 1. Existing local CFT tools -/

/-- The local Artin map (reused from the existing CFT port). -/
noncomputable def sourceLocalArtinMap
    (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type uK) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
    [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] :
    Kˣ →* Gal(↥(PadicField.maxAbelian K Ω) / K) :=
  PadicField.artin p K Ω

/-- The local Kummer map (reused from the existing CFT port). -/
noncomputable def sourceLocalKummerClass
    (n : ℕ) (K : Type uK) [Field K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [KummerTheory.HasKummerRoots n K Ω] [Algebra.IsIntegral K Ω] :
    Kˣ →* ContH1 Gal(Ω/K) (KummerTheory.Mu n Ω) :=
  KummerTheory.kummer n K Ω

/-! ## 2. The copy action on the Kummer classes -/

section CopyAction

variable (n : ℕ) (K : Type uK) [Field K]
variable (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
variable [KummerTheory.HasKummerRoots n K Ω] [Algebra.IsIntegral K Ω]

/-- The paper-faithful copy action of a local unit on the Kummer classes:
multiplication by its Kummer class (the Kummer map is multiplicative). -/
noncomputable def sourceKummerCopyEquiv (a : Kˣ) :
    ContH1 Gal(Ω/K) (KummerTheory.Mu n Ω) ≃
      ContH1 Gal(Ω/K) (KummerTheory.Mu n Ω) where
  toFun x := sourceLocalKummerClass n K Ω a * x
  invFun x := (sourceLocalKummerClass n K Ω a)⁻¹ * x
  left_inv x := by
    show (sourceLocalKummerClass n K Ω a)⁻¹ *
      (sourceLocalKummerClass n K Ω a * x) = x
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  right_inv x := by
    show sourceLocalKummerClass n K Ω a *
      ((sourceLocalKummerClass n K Ω a)⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- The copy action of the unit local unit is the identity. -/
theorem sourceKummerCopyEquiv_one :
    sourceKummerCopyEquiv n K Ω (1 : Kˣ) = Equiv.refl _ := by
  ext x
  show sourceLocalKummerClass n K Ω (1 : Kˣ) * x = x
  rw [map_one, one_mul]

/-- The copy action is multiplicative: the product copy acts as the composite of
the two copy actions. -/
theorem sourceKummerCopyEquiv_mul (a b : Kˣ) :
    sourceKummerCopyEquiv n K Ω (a * b) =
      (sourceKummerCopyEquiv n K Ω b).trans
        (sourceKummerCopyEquiv n K Ω a) := by
  ext x
  rw [Equiv.trans_apply]
  show sourceLocalKummerClass n K Ω (a * b) * x =
    sourceLocalKummerClass n K Ω a *
      (sourceLocalKummerClass n K Ω b * x)
  rw [map_mul, mul_assoc]

end CopyAction

/-! ## 3. The exact missing Galois-Kummer compatibility datum -/

/-- The exact missing datum matching the Kummer-class copy action with the
local Artin/Galois character (the Galois-Kummer compatibility of the (Ind2)
indeterminacy; page refs IUT III:616-620, Fig. I.5).  Recorded as data with a
compatibility law, not assumed. -/
structure SourceKummerArtinCompatibility
    (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type uK) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
    [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω]
    (n : ℕ) [KummerTheory.HasKummerRoots n K Ω] [Algebra.IsIntegral K Ω] where
  /-- the Galois-Kummer comparison on the local Kummer layer -/
  comparison : ContH1 Gal(Ω/K) (KummerTheory.Mu n Ω) →*
    Gal(↥(PadicField.maxAbelian K Ω) / K)
  /-- the comparison matches the actual Artin map of the Kummer class of every
  local unit copy -/
  comparison_kummer : ∀ a : Kˣ,
    comparison (sourceLocalKummerClass n K Ω a) =
      sourceLocalArtinMap p K Ω a

end LeanFormal.IUT.XiFPaper.S3139C2LocalKummerCopyActual

end
