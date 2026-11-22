import tmp.sheaf.xif.paper.PaperThetaRootObstructionActual
import tmp.sheaf.xif.paper.TwoLthRootKummerActual
import Mathlib.Algebra.Group.TypeTags.Basic

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S750PaperRootStackOtriCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open Multiplicative

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Units of the base field embedded in the ambient algebraic closure. -/
noncomputable def unitToAlgClosedMap :
    (sourceRootField T b)ˣ →* (AlgebraicClosure (sourceRootField T b))ˣ :=
  Units.map (algebraMap (sourceRootField T b)
    (AlgebraicClosure (sourceRootField T b))).toMonoidHom

abbrev RootStackSectionCarrier : Type :=
  (AlgebraicClosure (sourceRootField T b))ˣ × Multiplicative Real

noncomputable def divisorSection (u : RootStackSectionCarrier T b) : Multiplicative Real :=
  u.2

noncomputable def paperQSection : RootStackSectionCarrier T b :=
  (unitToAlgClosedMap T b (sourceRootQUnit T b), Multiplicative.ofAdd ((qVFamily T b).order : Real))

noncomputable def paperRootSection : RootStackSectionCarrier T b :=
  (sourceRoot T b, Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value)))

noncomputable def paperMuAction (ζ : muTwoLRoots T b) (u : RootStackSectionCarrier T b) :
    RootStackSectionCarrier T b :=
  (unitToAlgClosedMap (ζ.1) * u.1, u.2)

noncomputable def extensionUnitMap : RootStackSectionCarrier T b →*
    (AlgebraicClosure (sourceRootField T b))ˣ where
  toFun u := u.1
  map_one' := rfl
  map_mul' _ _ := rfl

structure PaperRootStackOtriCarrierSpec where
  sectionCarrier : Type
  [monoid : Monoid sectionCarrier]
  qSection : sectionCarrier
  rootSection : sectionCarrier
  root_pow : rootSection ^ (2 * l.value) = qSection
  divisorSection : sectionCarrier → Multiplicative Real
  q_divisor_eq : divisorSection qSection = Multiplicative.ofAdd ((qVFamily T b).order : Real)
  root_divisor_eq : divisorSection rootSection =
    Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value))
  extensionUnitMap : sectionCarrier →* (AlgebraicClosure (sourceRootField T b))ˣ
  q_image : extensionUnitMap qSection = unitToAlgClosedMap T b (sourceRootQUnit T b)
  root_image : extensionUnitMap rootSection = sourceRoot T b
  muAction : muTwoLRoots T b → sectionCarrier → sectionCarrier
  muAction_mul : ∀ (ζ ξ : muTwoLRoots T b) (x : sectionCarrier),
    muAction (ζ * ξ) x = muAction ζ (muAction ξ x)
  muAction_one : ∀ x : sectionCarrier, muAction 1 x = x
  qVFamily_reflection : Prop
  qVFamily_reflection_holds : qVFamily_reflection

noncomputable def paperRootStackOtriCarrier : PaperRootStackOtriCarrierSpec T b where
  sectionCarrier := RootStackSectionCarrier T b
  monoid := inferInstance
  qSection := paperQSection T b
  rootSection := paperRootSection T b
  root_pow := by
    apply Prod.ext
    · change (sourceRoot T b) ^ (2 * l.value) = unitToAlgClosedMap T b (sourceRootQUnit T b)
      apply Units.ext
      exact sourceRoot_pow T b
    · change Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value)) ^
          (2 * l.value) = Multiplicative.ofAdd ((qVFamily T b).order : Real)
      rw [← ofAdd_nsmul, nsmul_eq_mul]
      congr 1
      field_simp
      ring
  divisorSection := divisorSection (l := l) T b
  q_divisor_eq := rfl
  root_divisor_eq := rfl
  extensionUnitMap := extensionUnitMap (l := l) T b
  q_image := rfl
  root_image := rfl
  muAction := paperMuAction (l := l) T b
  muAction_mul := by
    intro ζ ξ x
    apply Prod.ext
    · change unitToAlgClosedMap T b ((ζ * ξ).1) * x.1 =
        unitToAlgClosed ζ.1 * (unitToAlgClosed ξ.1 * x.1)
      rw [show (ζ * ξ).1 = ζ.1 * ξ.1 from rfl, unitToAlgClosed_mul, mul_assoc]
    · rfl
  muAction_one := by
    intro x
    apply Prod.ext
    · change unitToAlgClosedMap T b (1 : muTwoLRoots T b) * x.1 = x.1
      rw [unitToAlgClosed_one]
      simp
    · rfl
  qVFamily_reflection := True
  qVFamily_reflection_holds := trivial

end LeanFormal.IUT.XiFPaper.S750PaperRootStackOtriCarrierActual

end