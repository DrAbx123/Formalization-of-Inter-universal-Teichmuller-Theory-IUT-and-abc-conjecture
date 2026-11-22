import tmp.sheaf.xif.paper.S815PaperScalingDataFiniteLActual
import tmp.sheaf.xif.paper.S201RootThetaNormLActual

-- S820: finite-L scaling generator from the S782 stack root unit.
-- Actual norm is ||stackRootUnit|| = e_i * p^(-cRoot_i); when e_i=1
-- this is an exact FiniteLScalingGenerator.  No fake e_i.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S820FiniteLScalingGeneratorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S815PaperScalingDataFiniteLActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The actual root unit in the finite root-stack extension L(mu_{2l}). -/
noncomputable def stackRootUnit : (rootStackExtension T b)ˣ :=
  (stackRootSection (l := l) T b).1

theorem stackRootUnit_ne_zero :
    ((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
      rootStackExtension T b) ≠ 0 :=
  Units.ne_zero (stackRootUnit (l := l) T b)

/-- Exact e_v factor: actual unit norm divided by the desired paper radius. -/
noncomputable def stackRootUnitFactor (i : qVFamTensorV) : Real :=
  ‖((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
      rootStackExtension T b)‖ /
    ((qVFamTensorP T b : Real) ^ (-(paperRootCoefficientFamily T b i)))

theorem stackRootUnitFactor_pos (i : qVFamTensorV) :
    0 < stackRootUnitFactor (l := l) T b i := by
  unfold stackRootUnitFactor
  have hnorm : 0 < ‖((stackRootUnit (l := l) T b :
      (rootStackExtension T b)ˣ) : rootStackExtension T b)‖ :=
    norm_pos_iff.mpr (stackRootUnit_ne_zero (l := l) T b)
  have hradius : 0 < (qVFamTensorP T b : Real) ^
      (-(paperRootCoefficientFamily T b i)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos) _
  exact div_pos hnorm hradius

theorem stackRootUnit_norm_factor (i : qVFamTensorV) :
    ‖((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
        rootStackExtension T b)‖ =
      stackRootUnitFactor (l := l) T b i *
        ((qVFamTensorP T b : Real) ^ (-(paperRootCoefficientFamily T b i))) := by
  unfold stackRootUnitFactor
  have hr : ((qVFamTensorP T b : Real) ^ (-(paperRootCoefficientFamily T b i))) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos) _)
  field_simp [hr]

/-- Finite-L generator up to the exact e_v factor. -/
structure FiniteLScalingGeneratorUpToFactor where
  generator : qVFamTensorV → rootStackExtension T b
  generator_ne_zero : ∀ i, generator i ≠ 0
  factor : qVFamTensorV → Real
  factor_pos : ∀ i, 0 < factor i
  norm_eq : ∀ i, ‖generator i‖ = factor i *
    ((qVFamTensorP T b : Real) ^ (-(paperRootCoefficientFamily T b i)))

noncomputable def stackFiniteLScalingGeneratorUpToFactor :
    FiniteLScalingGeneratorUpToFactor (l := l) T b where
  generator _ := ((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
    rootStackExtension T b)
  generator_ne_zero _ := stackRootUnit_ne_zero (l := l) T b
  factor := stackRootUnitFactor (l := l) T b
  factor_pos := stackRootUnitFactor_pos (l := l) T b
  norm_eq := stackRootUnit_norm_factor (l := l) T b

/-- If the exact e_v factor is one, the genuine FiniteLScalingGenerator exists. -/
noncomputable def finiteLScalingGenerator_of_factor_eq_one
    (h : ∀ i, stackRootUnitFactor (l := l) T b i = 1) :
    FiniteLScalingGenerator (l := l) T b := by
  refine
    { generator := fun _ =>
        ((stackRootUnit (l := l) T b : (rootStackExtension T b)ˣ) :
          (rootStackExtension T b))
      generator_ne_zero := fun _ => stackRootUnit_ne_zero (l := l) T b
      generator_norm := ?_ }
  intro i
  rw [stackRootUnit_norm_factor (l := l) T b i, h i, one_mul]

/-- Exact e_v factor condition; if true the scaling data exists by S815. -/
def StackRootUnitFactorOne : Prop :=
  ∀ i, stackRootUnitFactor (l := l) T b i = 1

theorem finiteLScalingGenerator_of_factorOne
    (h : StackRootUnitFactorOne (l := l) T b) :
    Nonempty (FiniteLScalingGenerator (l := l) T b) :=
  ⟨finiteLScalingGenerator_of_factor_eq_one (l := l) T b h⟩

#check stackRootUnit
#check stackRootUnitFactor
#check stackFiniteLScalingGeneratorUpToFactor
#check finiteLScalingGenerator_of_factor_eq_one

end LeanFormal.IUT.XiFPaper.S820FiniteLScalingGeneratorActual

end