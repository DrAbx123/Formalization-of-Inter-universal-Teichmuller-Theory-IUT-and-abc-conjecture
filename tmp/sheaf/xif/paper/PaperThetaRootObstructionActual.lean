import tmp.sheaf.n8.closure.C3Roots
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # q-parameter power q^(j^2) is not paper theta

Per PAPER_OBJECT_SPEC, paper theta is (QRoot_v)^(j^2), where QRoot_v is a
2l-th root of the q-parameter, and mu_{2l} acts by roots of unity.  This file's
q-parameter power paperQParameterThetaValue is explicitly only a q-side helper;
it is NOT paper theta and must not be used as such.

The q-root extension is retained only as an independent indeterminacy
structure.  No root of q is asserted to be paper theta. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual normalized completion field K of the qVFamily place. -/
abbrev sourceRootField : Type :=
  NormalizedCompletion (qVFamTensorPlace T b)

/-- The qVFamily q as an actual unit of K. -/
noncomputable def sourceRootQUnit : (sourceRootField T b)ˣ :=
  Units.mk0 ((qVFamily T b).q : sourceRootField T b)
    (by
      intro h
      exact (qVFamily T b).q_ne_zero h)

/-- q-PARAMETER power in K: q^(j^2).  This is not paper theta; paper
-- theta uses the root-valued q_v^(j^2) from PaperC3RootThetaHullActual. -/
noncomputable def paperQParameterThetaValue
    (j : SignedLabel l.value) : sourceRootField T b :=
  ((sourceRootQUnit T b : sourceRootField T b)) ^ ((gaussExponent j.1).toNat ^ 2)

/-- The paper theta value is the actual q-power. -/
theorem paperQParameterThetaValue_eq
    (j : SignedLabel l.value) :
    paperQParameterThetaValue T b j =
      ((sourceRootQUnit T b : sourceRootField T b)) ^
        ((gaussExponent j.1).toNat ^ 2) := rfl

/-- The actual mu_{2l} root-of-unity subgroup of K. -/
noncomputable def muTwoLRoots :
    Subgroup (sourceRootField T b)ˣ :=
  rootsOfUnity (2 * l.value) (sourceRootField T b)

/-- The actual mu_{2l} action on K by multiplication. -/
noncomputable def muTwoLRootAction
    (ζ : muTwoLRoots T b) (x : sourceRootField T b) : sourceRootField T b :=
  ((ζ : (sourceRootField T b)ˣ) : sourceRootField T b) * x

/-- The mu_{2l} action on the paper theta value is multiplication by the root
of unity. -/
theorem muTwoLRootAction_qParameterThetaValue
    (ζ : muTwoLRoots T b) (j : SignedLabel l.value) :
    muTwoLRootAction T b ζ (paperQParameterThetaValue T b j) =
      ((ζ : (sourceRootField T b)ˣ) : sourceRootField T b) *
        paperQParameterThetaValue T b j := rfl

/-- Actual mu_{2l} root-of-unity indeterminacy data. -/
structure MuTwoLIndeterminacyData where
  qParameterValue : SignedLabel l.value → sourceRootField T b
  qParameterValue_eq : qParameterValue = paperQParameterThetaValue T b
  action : muTwoLRoots T b → sourceRootField T b → sourceRootField T b
  action_eq : action = muTwoLRootAction T b
  action_qParameter : ∀ (ζ : muTwoLRoots T b) (j : SignedLabel l.value),
    action ζ (qParameterValue j) =
      ((ζ : (sourceRootField T b)ˣ) : sourceRootField T b) * qParameterValue j

/-- The actual mu_{2l} indeterminacy data constructor. -/
noncomputable def muTwoLIndeterminacyData :
    MuTwoLIndeterminacyData T b where
  qParameterValue := paperQParameterThetaValue T b
  qParameterValue_eq := rfl
  action := muTwoLRootAction T b
  action_eq := rfl
  action_qParameter := fun ζ j => rfl

/-! ## Independent q-root extension (indeterminacy only, not theta) -/

/-- The actual 2l-th root system of the qVFamily q candidate. -/
noncomputable def sourceRootSystem :
    NatRootSystem (unitToAlgClosed (sourceRootQUnit T b)) :=
  algClosedRootSystem (sourceRootQUnit T b)

/-- The actual 2l-th root in the algebraic closure. -/
noncomputable def sourceRoot : (AlgebraicClosure (sourceRootField T b))ˣ :=
  (sourceRootSystem T b).root (2 * l.value)

/-- The actual q-root extension, retained only as an independent indeterminacy
structure (not a theta value). -/
noncomputable def sourceRootExtension :
    IntermediateField (sourceRootField T b)
      (AlgebraicClosure (sourceRootField T b)) :=
  IntermediateField.adjoin (sourceRootField T b)
    {((sourceRoot T b : (AlgebraicClosure (sourceRootField T b))ˣ) :
      AlgebraicClosure (sourceRootField T b))}

/-- The root equation of the independent indeterminacy extension. -/
theorem sourceRoot_pow :
    ((sourceRoot T b : (AlgebraicClosure (sourceRootField T b))ˣ) :
      AlgebraicClosure (sourceRootField T b)) ^ (2 * l.value) =
      (unitToAlgClosed (sourceRootQUnit T b) :
        AlgebraicClosure (sourceRootField T b)) := by
  have h := NatRootSystem.pow_self (sourceRootSystem T b) (2 * l.value)
    (by
      have : 0 < 2 * l.value := Nat.mul_pos (by norm_num) l.prime.pos
      exact this.ne')
  simpa [sourceRoot, sourceRootSystem] using congrArg
    (fun z : (AlgebraicClosure (sourceRootField T b))ˣ =>
      (z : AlgebraicClosure (sourceRootField T b))) h

/-- Exact missing normalized completion/tensor-block API over the independent
root extension. -/
structure RootCompletionTensorBlockAPI where
  extension : IntermediateField (sourceRootField T b)
    (AlgebraicClosure (sourceRootField T b))
  finiteDimensional : Module.Finite (sourceRootField T b) extension
  normedField : NormedField extension
  measurableSpace : MeasurableSpace extension
  tensorBlock : Type
  tensorUnit : tensorBlock
  tensorLogVolume : tensorBlock → Real

/-- Exact missing API Prop; no inhabitant is asserted. -/
def RootCompletionTensorBlockAPIRequired : Prop :=
  Nonempty (RootCompletionTensorBlockAPI T b)

end LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual

end
