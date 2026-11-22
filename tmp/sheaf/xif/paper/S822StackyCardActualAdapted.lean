import tmp.sheaf.xif.paper.S816StackyHullInterfaceActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual

/-! # S822: card of mu_2l and actual HullLogEqStacky

Prove Nat.card(StackMuGroup)=2l using the primitive root `stackMuUnit` in the
finite root-stack extension, then derive HullLogEqStacky and inhabit
StackyHullLogInterface. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S822StackyCardActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S816StackyHullInterfaceActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S811StackMuPermActionActual
open LeanFormal.IUT.XiFPaper.S813PaperInterfaceHub
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

/-- The primitive root stack unit is primitive in the root-stack extension. -/
theorem stackMuUnit_isPrimitiveRoot :
    IsPrimitiveRoot ((stackMuUnit (l := l) T b : rootStackExtension T b))
      (2 * l.value) := by
  apply IsPrimitiveRoot.of_map_of_injective
    (f := fun x : rootStackExtension T b => (x : rootNormedAmbient T b))
  · change IsPrimitiveRoot
      (((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
        rootNormedAmbient T b)) (2 * l.value)
    unfold stackMuRoot
    exact Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot
      (rootNormedAmbient T b) (2 * l.value))
  · exact Subtype.coe_injective

/-- The mu_2l action group has cardinal 2l. -/
theorem stackMuGroup_card :
    Nat.card (StackMuGroup (l := l) T b) = 2 * l.value := by
  haveI : NeZero (2 * l.value) := ⟨Nat.mul_ne_zero (by norm_num) l.prime.ne_zero⟩
  exact stackMuUnit_isPrimitiveRoot (l := l) T b |>.card_rootsOfUnity

/-- The S816 exact bridge is actually true. -/
theorem hullLogEqStacky_actual :
    HullLogEqStacky (l := l) T b mu := by
  unfold HullLogEqStacky stackyVolume
  rw [stackMuGroup_card (l := l) T b]
  have hl : (2 * (l.value : Real)) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (by norm_num : (2:Nat) ≠ 0) l.prime.ne_zero)
  field_simp [hl]

/-- Actual inhabitant of the S813 stacky interface. -/
noncomputable def stackyHullLogInterface :
    StackyHullLogInterface (qVFamTensorBlock T b) :=
  stackyHullLogInterfaceOfBridge (l := l) T b mu
    (hullLogEqStacky_actual (l := l) T b mu)

end LeanFormal.IUT.XiFPaper.S822StackyCardActualAdapted
end
