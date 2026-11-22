import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiReductionActualConstruct
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

/-!
# Inhabited corrected actual minimal model

This file inhabits the corrected actual minimal model for the base-changed
source curve using Mathlib's `exists_isMinimal` and `integralModel`.  The
stored curve is integral over the adic completion integers, the stored change
is the actual Mathlib Weierstrass change, base change recovers the source curve
up to that change, and the changed curve is minimal.

The older raw `SourcePsiActualMinimalModel` requires equality of the raw
coefficients (no change).  That condition is strictly stronger and is not
inhabited here; the exact relation is recorded.  No model is fabricated.
-/

namespace LeanFormal.IUT.SourcePsiActualMinimalModelInhabited

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiReductionActualConstruct
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- Corrected actual minimal model: an integral curve, the actual Weierstrass
change, base change up to that change, and minimality of the changed curve. -/
structure SourcePsiActualMinimalModelCorrected where
  /-- Integral Weierstrass curve over the adic completion integers. -/
  curve : WeierstrassCurve (SourcePsiCompletionIntegers S v)
  /-- Actual Weierstrass change over the completion field. -/
  change : WeierstrassCurve.VariableChange (SourcePsiCompletionField S v)
  /-- Base change recovers the source curve up to the change. -/
  baseChange_eq : curve⁄(SourcePsiCompletionField S v) =
    change • SourcePsiBaseChangedCurve S v
  /-- The changed source curve is minimal over the adic completion integers. -/
  minimal : WeierstrassCurve.IsMinimal (SourcePsiCompletionIntegers S v)
    (change • SourcePsiBaseChangedCurve S v)

/-- Actual inhabitant constructed from Mathlib's minimal-model theorem. -/
noncomputable def sourcePsiActualMinimalModelCorrected :
    SourcePsiActualMinimalModelCorrected S v := by
  classical
  let R := SourcePsiCompletionIntegers S v
  let K := SourcePsiCompletionField S v
  let W := SourcePsiBaseChangedCurve S v
  let h := WeierstrassCurve.exists_isMinimal (R := R) (K := K) W
  let C : WeierstrassCurve.VariableChange K := Classical.choose h
  let hmin : WeierstrassCurve.IsMinimal R (C • W) := Classical.choose_spec h
  let hInt : WeierstrassCurve.IsIntegral R (C • W) :=
    WeierstrassCurve.IsMinimal.isIntegral R (C • W)
  let Wint : WeierstrassCurve R := WeierstrassCurve.integralModel R (C • W)
  have hbase : Wint⁄K = C • W :=
    WeierstrassCurve.baseChange_integralModel_eq R (C • W)
  exact { curve := Wint, change := C, baseChange_eq := hbase, minimal := hmin }

theorem sourcePsiActualMinimalModelCorrected_baseChange :
    (sourcePsiActualMinimalModelCorrected S v).curve⁄
        (SourcePsiCompletionField S v) =
      (sourcePsiActualMinimalModelCorrected S v).change •
        SourcePsiBaseChangedCurve S v :=
  (sourcePsiActualMinimalModelCorrected S v).baseChange_eq

theorem sourcePsiActualMinimalModelCorrected_minimal :
    WeierstrassCurve.IsMinimal (SourcePsiCompletionIntegers S v)
      ((sourcePsiActualMinimalModelCorrected S v).change •
        SourcePsiBaseChangedCurve S v) :=
  (sourcePsiActualMinimalModelCorrected S v).minimal

theorem sourcePsiActualMinimalModelCorrected_integral :
    WeierstrassCurve.IsIntegral (SourcePsiCompletionIntegers S v)
      ((sourcePsiActualMinimalModelCorrected S v).change •
        SourcePsiBaseChangedCurve S v) :=
  WeierstrassCurve.IsMinimal.isIntegral (SourcePsiCompletionIntegers S v)
    ((sourcePsiActualMinimalModelCorrected S v).change •
      SourcePsiBaseChangedCurve S v)

/-- A corrected datum with trivial change is an old raw model. -/
noncomputable def correctedToRaw
    (A : SourcePsiActualMinimalModelCorrected S v) (h : A.change = 1) :
    SourcePsiIntegralModelData S v where
  curve := A.curve
  baseChange_eq := by rw [A.baseChange_eq, h, one_smul]


/-- The corrected minimal model is inhabited. -/
theorem sourcePsiActualMinimalModelCorrected_nonempty :
    Nonempty (SourcePsiActualMinimalModelCorrected S v) :=
  ⟨sourcePsiActualMinimalModelCorrected S v⟩

/-- The corrected model's reduced curve over the residue field. -/
noncomputable def correctedReducedCurve
    (A : SourcePsiActualMinimalModelCorrected S v) :
    WeierstrassCurve (IsLocalRing.ResidueField (SourcePsiCompletionIntegers S v)) :=
  A.curve.map (IsLocalRing.residue (SourcePsiCompletionIntegers S v))

theorem correctedReducedCurve_eq_map
    (A : SourcePsiActualMinimalModelCorrected S v) :
    correctedReducedCurve S v A =
      A.curve.map (IsLocalRing.residue (SourcePsiCompletionIntegers S v)) :=
  rfl


/-- Exact obstruction: the old raw `SourcePsiActualMinimalModel` cannot be
inhabited from Mathlib's minimal model without an additional proof that the
actual Weierstrass change is trivial.  This is a Prop, not a fake model. -/
def SourcePsiRawTrivialChangeObstruction : Prop :=
  Nonempty {A : SourcePsiActualMinimalModelCorrected S v // A.change = 1}

/-- The corrected minimal model is the actual Mathlib construction; the raw
obstruction remains exactly the trivial-change condition. -/
theorem sourcePsiActualMinimalModelCorrected_holds :
    Nonempty (SourcePsiActualMinimalModelCorrected S v) ∧
      (sourcePsiActualMinimalModelCorrected S v).curve⁄
          (SourcePsiCompletionField S v) =
        (sourcePsiActualMinimalModelCorrected S v).change •
          SourcePsiBaseChangedCurve S v :=
  ⟨sourcePsiActualMinimalModelCorrected_nonempty S v,
    sourcePsiActualMinimalModelCorrected_baseChange S v⟩

/-! ## Reduced curve coefficient laws

/-- The reduced a1 is the residue of the minimal model's a1. -/
theorem correctedReducedCurve_a₁
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (correctedReducedCurve S v A).a₁ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.a₁ :=
  rfl

theorem correctedReducedCurve_a₂
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (correctedReducedCurve S v A).a₂ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.a₂ :=
  rfl

theorem correctedReducedCurve_a₃
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (correctedReducedCurve S v A).a₃ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.a₃ :=
  rfl

theorem correctedReducedCurve_a₄
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (correctedReducedCurve S v A).a₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.a₄ :=
  rfl

theorem correctedReducedCurve_a₆
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (correctedReducedCurve S v A).a₆ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.a₆ :=
  rfl

theorem correctedReducedCurve_Δ
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (correctedReducedCurve S v A).Δ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.Δ :=
  WeierstrassCurve.map_Δ

theorem correctedReducedCurve_c₄
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (correctedReducedCurve S v A).c₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.c₄ :=
  WeierstrassCurve.map_c₄

theorem correctedReducedCurve_b₂
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (correctedReducedCurve S v A).b₂ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.b₂ :=
  WeierstrassCurve.map_b₂

theorem correctedReducedCurve_b₄
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (correctedReducedCurve S v A).b₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.b₄ :=
  WeierstrassCurve.map_b₄

theorem correctedReducedCurve_b₆
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (correctedReducedCurve S v A).b₆ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.b₆ :=
  WeierstrassCurve.map_b₆

theorem correctedReducedCurve_b₈
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (correctedReducedCurve S v A).b₈ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.b₈ :=
  WeierstrassCurve.map_b₈

/-! ## Connection with the existing reduced curve and identification

/-- With trivial change, the corrected reduced curve is the existing
`SourcePsiReducedCurve` of the raw model. -/
theorem correctedReducedCurve_eq_raw
    (A : SourcePsiActualMinimalModelCorrected S v) (h : A.change = 1) :
    correctedReducedCurve S v A =
      SourcePsiReducedCurve S v (correctedToRaw S v A h) :=
  rfl

/-- With trivial change, the corrected model gives an actual reduction
identification for the raw model. -/
noncomputable def correctedReductionIdentification
    (A : SourcePsiActualMinimalModelCorrected S v) (h : A.change = 1) :
    SourcePsiReductionIdentification S v (correctedToRaw S v A h) where
  specialFiber_eq := correctedReducedCurve S v A
  specialFiber_eq_reduced := rfl

theorem correctedReductionIdentification_specialFiber_eq
    (A : SourcePsiActualMinimalModelCorrected S v) (h : A.change = 1) :
    (correctedReductionIdentification S v A h).specialFiber_eq =
      SourcePsiReducedCurve S v (correctedToRaw S v A h) :=
  rfl

/-! ## Exact raw trivial-change obstruction

/-- The old raw actual-minimal-model residual. -/
def SourcePsiRawActualMinimalModelResidual : Prop :=
  Nonempty (SourcePsiActualMinimalModel S v)

/-- A corrected model with trivial change plus the project's corrected
minimality condition gives the old raw actual minimal model. -/
noncomputable def rawActualMinimalModelOfTrivialChange
    (A : SourcePsiActualMinimalModelCorrected S v) (h : A.change = 1)
    (hmin : SourcePsiIntegralModelMinimalCorrected S v (correctedToRaw S v A h)) :
    SourcePsiActualMinimalModel S v where
  model := correctedToRaw S v A h
  minimal := hmin

/-- The exact obstruction statement: the raw residual is equivalent to the
existence of a corrected model with trivial change and the project corrected
minimality condition.  This is a proposition, not an assumed model. -/
def SourcePsiRawTrivialChangeAndMinimalityObstruction : Prop :=
  ∃ A : SourcePsiActualMinimalModelCorrected S v,
    A.change = 1 ∧
      SourcePsiIntegralModelMinimalCorrected S v (correctedToRaw S v A)

theorem rawActualMinimalModelResidual_of_obstruction
    (h : SourcePsiRawTrivialChangeAndMinimalityObstruction S v) :
    SourcePsiRawActualMinimalModelResidual S v := by
  rcases h with ⟨A, hchange, hmin⟩
  exact ⟨rawActualMinimalModelOfTrivialChange S v A hchange hmin⟩


end LeanFormal.IUT.SourcePsiActualMinimalModelInhabited
end
end LeanFormal.IUT.SourcePsiActualMinimalModelInhabited
end