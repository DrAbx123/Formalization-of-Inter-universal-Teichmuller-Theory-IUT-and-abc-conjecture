import tmp.sheaf.xif.paper.S759LSectionCarrierCorrectionActual
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S759LSectionCarrierCorrectionActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- A primitive 2l-th root of unity in the ambient algebraic closure. -/
noncomputable def stackMuRoot : (rootNormedAmbient T b)ˣ :=
  let ζ := Classical.choose (HasEnoughRootsOfUnity.exists_primitiveRoot
    (rootNormedAmbient T b) (2 * l.value))
  let hζ := Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot
    (rootNormedAmbient T b) (2 * l.value))
  Units.mk0 ζ (hζ.ne_zero (by
    exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero))

theorem stackMuRoot_pow :
    ((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
      rootNormedAmbient T b) ^ (2 * l.value) = 1 := by
  unfold stackMuRoot
  exact (Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot
    (rootNormedAmbient T b) (2 * l.value))).pow_eq_one

/-- The finite root-stack extension L(mu_{2l}). -/
noncomputable def rootStackExtension :
    IntermediateField (rootNormedExtension T b) (rootNormedAmbient T b) :=
  IntermediateField.adjoin (rootNormedExtension T b)
    ({((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
      rootNormedAmbient T b)} : Set (rootNormedAmbient T b))

theorem rootStackExtension_finiteDimensional :
    Module.Finite (rootNormedExtension T b) (rootStackExtension T b) := by
  unfold rootStackExtension
  apply IntermediateField.adjoin.finiteDimensional
  have h2l : 0 < 2 * l.value := Nat.mul_pos (by norm_num) l.prime.pos
  have hpow : IsIntegral (rootNormedExtension T b)
      (((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
        rootNormedAmbient T b) ^ (2 * l.value)) := by
    rw [stackMuRoot_pow T b]
    exact isIntegral_one
  exact IsIntegral.of_pow h2l hpow

noncomputable instance rootStackFiniteDimensionalK :
    FiniteDimensional (rootBase T b) (rootStackExtension T b) := by
  letI : FiniteDimensional (rootNormedExtension T b) (rootStackExtension T b) :=
    rootStackExtension_finiteDimensional T b
  letI : FiniteDimensional (rootBase T b) (rootNormedExtension T b) :=
    rootNormedExtensionFiniteDimensional T b
  exact FiniteDimensional.trans (rootBase T b) (rootNormedExtension T b)
    (rootStackExtension T b)

noncomputable instance rootStackComplete :
    CompleteSpace (rootStackExtension T b) := by
  letI : CompleteSpace (rootBase T b) := inferInstance
  letI : NormedSpace (rootBase T b) (rootStackExtension T b) := inferInstance
  letI : FiniteDimensional (rootBase T b) (rootStackExtension T b) :=
    rootStackFiniteDimensionalK T b
  exact FiniteDimensional.complete (rootBase T b) (rootStackExtension T b)

noncomputable instance rootStackProper :
    ProperSpace (rootStackExtension T b) := by
  letI : NormedSpace (rootBase T b) (rootStackExtension T b) := inferInstance
  letI : FiniteDimensional (rootBase T b) (rootStackExtension T b) :=
    rootStackFiniteDimensionalK T b
  exact FiniteDimensional.proper (rootBase T b) (rootStackExtension T b)

noncomputable instance rootStackMeasurableSpace :
    MeasurableSpace (rootStackExtension T b) :=
  borel (rootStackExtension T b)

noncomputable instance rootStackBorelSpace :
    BorelSpace (rootStackExtension T b) := ⟨rfl⟩

/-- Units of L mapped into the finite root-stack extension. -/
noncomputable def stackLUnitMap : (rootNormedExtension T b)ˣ →* (rootStackExtension T b)ˣ :=
  Units.map (algebraMap (rootNormedExtension T b) (rootStackExtension T b)).toMonoidHom

/-- Finite root-stack carrier: extension units times a real divisor coordinate. -/
abbrev StackSectionCarrier : Type :=
  (rootStackExtension T b)ˣ × Multiplicative Real

noncomputable def stackDivisorSection (u : StackSectionCarrier T b) : Multiplicative Real :=
  u.2

noncomputable def stackQSection : StackSectionCarrier T b :=
  (stackLUnitMap T b (rootNormedUnit T b ^ (2 * l.value)),
    Multiplicative.ofAdd ((qVFamily T b).order : Real))

noncomputable def stackRootSection : StackSectionCarrier T b :=
  (stackLUnitMap T b (rootNormedUnit T b),
    Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value)))

theorem stackRootSection_pow :
    stackRootSection T b ^ (2 * l.value) = stackQSection T b := by
  apply Prod.ext
  · change (stackLUnitMap T b (rootNormedUnit T b)) ^ (2 * l.value) =
      stackLUnitMap T b (rootNormedUnit T b ^ (2 * l.value))
    exact (map_pow (stackLUnitMap T b) (rootNormedUnit T b) (2 * l.value)).symm
  · change Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value)) ^
        (2 * l.value) = Multiplicative.ofAdd ((qVFamily T b).order : Real)
    rw [← ofAdd_nsmul, nsmul_eq_mul]
    congr 1
    have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
    field_simp [hl]
    push_cast
    ring

/-- The primitive root of unity as a unit of the finite root-stack extension. -/
noncomputable def stackMuUnit : (rootStackExtension T b)ˣ :=
  Units.mk0
    ⟨((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
      rootNormedAmbient T b),
      IntermediateField.subset_adjoin (rootNormedExtension T b)
        ({((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
          rootNormedAmbient T b)} : Set (rootNormedAmbient T b))
        (Set.mem_singleton _)⟩
    (by
      intro h
      have hzero : (((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
          rootNormedAmbient T b)) = 0 := congrArg Subtype.val h
      exact Units.ne_zero (stackMuRoot (l := l) T b) hzero)

/-- mu_{2l} action on the finite root-stack carrier. -/
noncomputable def stackMuAction (u : StackSectionCarrier T b) : StackSectionCarrier T b :=
  (stackMuUnit T b * u.1, u.2)

/-- Inherited additive Haar on the finite root-stack extension. -/
noncomputable def rootStackHaar : Measure (rootStackExtension T b) :=
  Measure.addHaar

end LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual

end
