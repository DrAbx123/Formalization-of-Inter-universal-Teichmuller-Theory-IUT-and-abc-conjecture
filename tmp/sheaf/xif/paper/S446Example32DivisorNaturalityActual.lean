import tmp.sheaf.xif.paper.S433Example32RationalDivisorActual
import tmp.sheaf.xif.paper.S442DvCoverNormPullbackActual

/-!
# S446: conditional Example 3.2 divisor naturality

Given S412 normalized valuations V on L and V' on L' and the S442 norm-valuation
compatibility, the S433 divisor coefficients satisfy

  divisorCoefficient_L V (normPullback f x) = divisorCoefficient_L' V' x.

The S398 cover-level conditional structure and the exact missing bridge from
DvTriangleFieldCover category morphisms to explicit K-algebra maps are recorded.
No fake naturality and no fake valuation compatibility.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

namespace LeanFormal.IUT.XiFPaper.S446Example32DivisorNaturalityActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual
open LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual
open LeanFormal.IUT.XiFPaper.S433Example32RationalDivisorActual
open LeanFormal.IUT.XiFPaper.S442DvCoverNormPullbackActual

universe u

variable {K : Type u} [Field K]

section Generic

variable {L L' : Type u} [Field L] [Field L'] [Algebra K L] [Algebra K L']
variable (V : DvCoverNormalizedValuationData K L)
variable (V' : DvCoverNormalizedValuationData K L')
variable (f : L →ₐ[K] L')

/-- Generic normalized divisor coefficient (the same formula as S433). -/
def divisorCoefficientOfValuation (x : Lˣ) : ℤ :=
  Multiplicative.toAdd (V.valuation x)

/-- Conditional divisor naturality: norm pullback changes the divisor
coefficient by the valuation compatibility. -/
theorem example32DivisorCoefficient_normPullback
    (h : DvCoverNormValuationCompatibility V V' f) (x : L'ˣ) :
    divisorCoefficientOfValuation V (normPullback f x) =
      divisorCoefficientOfValuation V' x := by
  simp [divisorCoefficientOfValuation, h.norm_valuation x]

end Generic

section DvTriangle

variable (L L' : DvTriangleFieldCover K)
variable [Field L.obj.obj] [Algebra K L.obj.obj]
variable [Field L'.obj.obj] [Algebra K L'.obj.obj]
variable (V : DvCoverNormalizedValuationData K L.obj.obj)
variable (V' : DvCoverNormalizedValuationData K L'.obj.obj)
variable (f : L.obj.obj →ₐ[K] L'.obj.obj)

/-- S398 cover-level conditional divisor-naturality package. -/
structure DvTriangleDivisorNaturalityData where
  compatibility : DvCoverNormValuationCompatibility V V' f
  divisor_naturality : ∀ x : L'.obj.objˣ,
    example32DivisorCoefficient (L := L) V (normPullback f x) =
      example32DivisorCoefficient (L := L') V' x

/-- Constructor from the norm-valuation compatibility. -/
theorem dvTriangleDivisorNaturalityData
    (h : DvCoverNormValuationCompatibility V V' f) :
    DvTriangleDivisorNaturalityData L L' V V' f where
  compatibility := h
  divisor_naturality := by
    intro x
    change divisorCoefficientOfValuation V (normPullback f x) =
      divisorCoefficientOfValuation V' x
    exact example32DivisorCoefficient_normPullback V V' f h x

end DvTriangle

/-- Exact missing bridge: DvTriangleFieldCover category morphisms to explicit
K-algebra maps of the underlying fields. -/
structure DvTriangleCategoryMorphismToAlgHomBridge
    (K : Type u) [Field K] where
  toAlgHom : ∀ {L L' : DvTriangleFieldCover K}
    [Field L.obj.obj] [Algebra K L.obj.obj]
    [Field L'.obj.obj] [Algebra K L'.obj.obj]
    (f : L ⟶ L'), L.obj.obj →ₐ[K] L'.obj.obj

/-- Exact missing datum: all per-cover S412 valuation data together with the
morphism bridge and norm-valuation compatibility. -/
structure Example32DivisorNaturalityFamily
    (K : Type u) [Field K] where
  valuation : ∀ (L : DvTriangleFieldCover K)
    [Field L.obj.obj] [Algebra K L.obj.obj],
      DvCoverNormalizedValuationData K L.obj.obj
  bridge : DvTriangleCategoryMorphismToAlgHomBridge K
  compatibility : ∀ {L L' : DvTriangleFieldCover K}
    [Field L.obj.obj] [Algebra K L.obj.obj]
    [Field L'.obj.obj] [Algebra K L'.obj.obj]
    (f : L ⟶ L'),
      DvCoverNormValuationCompatibility
        (valuation L) (valuation L') (bridge.toAlgHom f)

/-- Conditional full divisor naturality along DvTriangleFieldCover category
morphisms, given the exact missing valuation family, morphism bridge, and
norm-valuation compatibility. -/
theorem example32DivisorNaturality_from_family
    (h : Example32DivisorNaturalityFamily K)
    {L L' : DvTriangleFieldCover K}
    [Field L.obj.obj] [Algebra K L.obj.obj]
    [Field L'.obj.obj] [Algebra K L'.obj.obj]
    (f : L ⟶ L') (x : L'.obj.objˣ) :
    example32DivisorCoefficient (L := L) (h.valuation L)
        (normPullback (h.bridge.toAlgHom f) x) =
      example32DivisorCoefficient (L := L') (h.valuation L') x := by
  change divisorCoefficientOfValuation (h.valuation L)
      (normPullback (h.bridge.toAlgHom f) x) =
    divisorCoefficientOfValuation (h.valuation L') x
  exact example32DivisorCoefficient_normPullback
    (h.valuation L) (h.valuation L') (h.bridge.toAlgHom f)
    (h.compatibility f) x

/-- Exact-missing predicate for the full family. -/
def Example32DivisorNaturalityFamilyRequired : Prop :=
  Nonempty (Example32DivisorNaturalityFamily K)

end LeanFormal.IUT.XiFPaper.S446Example32DivisorNaturalityActual

end
