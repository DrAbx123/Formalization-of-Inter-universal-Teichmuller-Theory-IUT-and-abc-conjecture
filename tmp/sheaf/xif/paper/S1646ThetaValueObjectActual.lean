import tmp.sheaf.xif.paper.S1484ThetaObjectActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1646ThetaValueObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Foundations.Theta
open ABCBridge.SourceQlThetaPunctureIdeal
open ABCBridge.S1423ThetaInvertibleActual
open ABCBridge.SourceQlThetaLineBundleFromCurve
open ABCBridge.S1401ThetaLineBundleActual
open ABCBridge.S1424ThetaSectionActual
open ABCBridge.S1484ThetaObjectActual
open WeierstrassCurve.Affine

universe u
variable {l : PrimeGeFive} (S : SourceDefinition31Data.{u} l)
variable {x y : S.arithmetic.F} (h : (s1423Model S).Nonsingular x y)

/-- The actual generator `X - x` of the point ideal `I_P`. -/
noncomputable def s1646PointIdealXGenerator :
    s1484PointIdealModule S h :=
  ⟨CoordinateRing.XClass (s1423Model S) x, by
    apply Ideal.subset_span
    simp [CoordinateRing.XYIdeal]⟩

/-- The actual theta section value at the point P evaluated on the point-ideal
generator, raised to the Gaussian label weight j^2. -/
noncomputable def s1646ThetaSectionValue
    (j : SignedLabel l.value) : s1423Ring S :=
  ((s1484ThetaSectionAt S h) (s1646PointIdealXGenerator S h)) ^
    (gaussExponent j.1).toNat

theorem s1646ThetaSectionValue_apply
    (j : SignedLabel l.value) :
    s1646ThetaSectionValue S h j =
      (((s1646PointIdealXGenerator S h : s1484PointIdealModule S h) :
          s1423Ring S)) ^ (gaussExponent j.1).toNat := rfl

/-- Actual theta-section-value object at a curve point: the section evaluated
on the point-ideal generator, with label powers. -/
structure ThetaSectionValueObject where
  valueAtLabel : SignedLabel l.value → s1423Ring S
  valueAtLabel_eq : ∀ j,
    valueAtLabel j =
      (((s1646PointIdealXGenerator S h : s1484PointIdealModule S h) :
          s1423Ring S)) ^ (gaussExponent j.1).toNat

noncomputable def s1646ThetaSectionValueObject :
    ThetaSectionValueObject S h where
  valueAtLabel := s1646ThetaSectionValue S h
  valueAtLabel_eq := fun _ => rfl

/-- Exact first missing structure for a real theta section value: a map from
the actual coordinate-ring section values to the real value field plus its
normalization comparison.  No inhabitant is asserted. -/
structure RealThetaSectionValueObject where
  valueAtLabel : SignedLabel l.value → Real
  ringToReal : s1423Ring S → Real
  valueAtLabel_eq : ∀ j,
    valueAtLabel j = ringToReal (s1646ThetaSectionValue S h j)
  normalization : Real
  normalization_ne_zero : normalization ≠ 0

def S1646RealThetaSectionValueRequired : Prop :=
  Nonempty (RealThetaSectionValueObject S h)

end LeanFormal.IUT.XiFPaper.S1646ThetaValueObjectActual

end
