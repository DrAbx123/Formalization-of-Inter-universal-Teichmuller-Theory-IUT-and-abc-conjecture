import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceGaloisLogShell
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitGaloisDescent
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import Mathlib.FieldTheory.KrullTopology

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm

namespace S2035Probe5

variable (v : FinitePrimePlace 2 7)
local instance : Fact (Nat.Prime v.1) := ⟨v.2.2.2⟩

abbrev QPlace (v : FinitePrimePlace 2 7) : NumberField.FinitePlace ℚ :=
  rationalFinitePlace v.1

abbrev Kv (v : FinitePrimePlace 2 7) : Type := NormalizedCompletion (QPlace v)
abbrev Lv (v : FinitePrimePlace 2 7) : Type := SourceAlgebraicClosure (QPlace v)
abbrev Gv (v : FinitePrimePlace 2 7) : Type := Lv v ≃ₐ[Kv v] Lv v
abbrev LocalUnits (v : FinitePrimePlace 2 7) : Type := (AlgebraicClosure ℚ_[v.1])ˣ

noncomputable def completionBridge :
    Completion (QPlace v) ≃+* (rationalHeightOneSpectrum v.1).adicCompletion ℚ :=
  RingEquiv.cast (rationalFinitePlace_underlyingPrime v.1)

noncomputable def completionPadicEquiv :
    ℚ_[v.1] ≃+* Kv v :=
  (rationalFinitePlacePadicEquiv v.1).toRingEquiv.trans
    ((completionBridge v).symm.trans (normalizedCompletionRingEquiv (QPlace v)).symm)

noncomputable def eAlgClosure :
    AlgebraicClosure ℚ_[v.1] ≃+* Lv v :=
  IsAlgClosure.equivOfEquiv (L := AlgebraicClosure ℚ_[v.1]) (M := Lv v)
    (S := ℚ_[v.1]) (R := Kv v) (completionPadicEquiv v)

-- conjugation of Gv to LocalAbsoluteGalois
noncomputable def galoisConj (σ : Gv v) : LocalAbsoluteGalois v.1 :=
  AlgEquiv.ofRingEquiv
    (f := (eAlgClosure v).symm.toRingEquiv.comp
      (σ.toRingEquiv.comp (eAlgClosure v).toRingEquiv)) (by
      intro x
      have he : eAlgClosure v (algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1]) x) =
          algebraMap (Kv v) (Lv v) (completionPadicEquiv v x) :=
        IsAlgClosure.equivOfEquiv_algebraMap _ _ _ x
      rw [RingEquiv.comp_apply, RingEquiv.comp_apply, he, σ.commutes]
      exact IsAlgClosure.equivOfEquiv_symm_algebraMap _ _ _ x)

noncomputable def galoisConjSymm (τ : LocalAbsoluteGalois v.1) : Gv v :=
  AlgEquiv.ofRingEquiv
    (f := (eAlgClosure v).toRingEquiv.comp
      (τ.toRingEquiv.comp (eAlgClosure v).symm.toRingEquiv)) (by
      intro y
      have hs : (eAlgClosure v).symm (algebraMap (Kv v) (Lv v) y) =
          algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1]) ((completionPadicEquiv v).symm y) :=
        IsAlgClosure.equivOfEquiv_symm_algebraMap _ _ _ y
      rw [RingEquiv.comp_apply, RingEquiv.comp_apply, hs, τ.commutes]
      exact IsAlgClosure.equivOfEquiv_algebraMap _ _ _ ((completionPadicEquiv v).symm y))

noncomputable def GvEquiv : Gv v ≃* LocalAbsoluteGalois v.1 where
  toFun := galoisConj v
  invFun := galoisConjSymm v
  left_inv σ := by
    apply AlgEquiv.ext
    intro x
    simp [galoisConj, galoisConjSymm]
  right_inv τ := by
    apply AlgEquiv.ext
    intro x
    simp [galoisConj, galoisConjSymm]
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    simp [galoisConj]

-- unit equivalence
noncomputable def unitsEquiv : (Lv v)ˣ ≃* LocalUnits v :=
  Units.mapEquiv (eAlgClosure v).symm.toMulEquiv

-- actual action
noncomputable def actualAction : Gv v →* MulAut ((Lv v)ˣ) where
  toFun σ := Units.mapEquiv σ.toRingEquiv.toMulEquiv
  map_one' := by ext u; rfl
  map_mul' σ τ := by ext u; rfl

-- model action
noncomputable def localAction : LocalAbsoluteGalois v.1 →* MulAut (LocalUnits v) where
  toFun σ := Units.mapEquiv σ.toRingEquiv.toMulEquiv
  map_one' := by ext u; rfl
  map_mul' σ τ := by ext u; rfl

-- action compatibility
theorem unitsEquiv_action (σ : Gv v) (u : (Lv v)ˣ) :
    unitsEquiv v (actualAction v σ u) =
      localAction v (GvEquiv v σ) (unitsEquiv v u) := by
  apply Units.ext
  simp [unitsEquiv, actualAction, localAction, GvEquiv, galoisConj]

-- actual O_v units model
noncomputable def actualOUnitsPadicEquiv :
    (CompletionIntegers (QPlace v))ˣ ≃* ℤ_[(⟨v.1, v.2.2.2⟩ : Nat.Primes)]ˣ :=
  (Units.mapEquiv (RingEquiv.cast (rationalFinitePlace_underlyingPrime v.1)).toMulEquiv).trans
    (((PadicInt.adicCompletionIntegersEquiv (R := NumberField.RingOfIntegers ℚ)
      (⟨v.1, v.2.2.2⟩ : Nat.Primes)).symm).toMulEquiv)

end S2035Probe5
