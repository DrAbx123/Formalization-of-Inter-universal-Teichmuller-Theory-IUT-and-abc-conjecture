import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.OModuleCompactnessLayer
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSharedBoundary
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier

/-!
# Actual O-module / arithmetic vector-bundle / localization layer for SHE xi-c/xi-d

The carriers are the actual number-field integral ring, its completed valuation
rings, and its adic completions.  No arbitrary carrier is introduced.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT

namespace PaperOModuleLayer

variable {k : Type} [Field k] [NumberField k]

/-- The actual global integral ring O_k. -/
abbrev GlobalRing (k : Type) [Field k] [NumberField k] : Type :=
  NumberField.RingOfIntegers k

/-- The actual global sections of the trivial rank-r arithmetic module. -/
abbrev ModuleCarrier (k : Type) [Field k] [NumberField k] (r : Nat) : Type :=
  Fin r → GlobalRing k

/-- The actual completed valuation ring O_v at a finite place. -/
abbrev LocalRing (k : Type) [Field k] [NumberField k]
    (v : NumberField.FinitePlace k) : Type :=
  NumberFieldFinitePlace.CompletionIntegers v

/-- The actual local field K_v at a finite place. -/
abbrev LocalField (k : Type) [Field k] [NumberField k]
    (v : NumberField.FinitePlace k) : Type :=
  NumberFieldFinitePlace.Completion v

/-- The actual algebra map from O_k into the completed valuation ring O_v. -/
def completionAlg (v : NumberField.FinitePlace k) :
    GlobalRing k →+* LocalRing (k := k) v :=
  algebraMap (GlobalRing k) (LocalRing (k := k) v)

/-- Componentwise localization of a global section, summed in O_v. -/
def localization (r : Nat) (v : NumberField.FinitePlace k)
    (s : ModuleCarrier (k := k) r) : LocalRing (k := k) v :=
  Finset.univ.sum fun i : Fin r => completionAlg (k := k) v (s i)

/-- The actual rank datum. -/
def rank (r : Nat) : Nat := r

/-- The determinant line carrier of the trivial rank-r module is O_k. -/
abbrev DeterminantCarrier (k : Type) [Field k] [NumberField k] : Type :=
  GlobalRing k

/-- The determinant localization O_k to O_v. -/
def determinantLocalization (v : NumberField.FinitePlace k) :
    DeterminantCarrier (k := k) →+* LocalRing (k := k) v :=
  completionAlg (k := k) v

/-- The additive valuation of the completion, as an integer. -/
def localValuation (v : NumberField.FinitePlace k)
    (x : LocalField (k := k) v) : Int :=
  (Valued.v x).log

/-- The actual p-adic local log-volume of a determinant-line section, normalized
by the residue characteristic of the place. -/
def localLogVolume (v : NumberField.FinitePlace k)
    (d : DeterminantCarrier (k := k)) : Real :=
  - (localValuation (k := k) v
      ((algebraMap k (LocalField (k := k) v))
        (algebraMap (GlobalRing k) k d)) : Real) *
    Real.log (NumberFieldFinitePlace.residueCharacteristic v)

/-- The global log-volume over a selected finite set of places. -/
def logVolume (selected : Finset (NumberField.FinitePlace k))
    (d : DeterminantCarrier (k := k)) : Real :=
  selected.sum fun v => localLogVolume (k := k) v d

/-- Structural bundle data over the actual integral/completed carriers. -/
structure PaperOModuleLayerData (r : Nat)
    (selected : Finset (NumberField.FinitePlace k)) where
  rank : Nat
  moduleCarrier : Type
  localRing : NumberField.FinitePlace k → Type
  localField : NumberField.FinitePlace k → Type
  localization : (v : NumberField.FinitePlace k) → moduleCarrier → localRing v
  determinantCarrier : Type
  determinantLocalization : (v : NumberField.FinitePlace k) →
    determinantCarrier → localRing v
  localLogVolume : (v : NumberField.FinitePlace k) → determinantCarrier → Real
  logVolume : determinantCarrier → Real

/-- The actual data instance built from O_k, O_v, K_v and the completion maps. -/
def actualPaperOModuleLayerData (r : Nat)
    (selected : Finset (NumberField.FinitePlace k)) :
    PaperOModuleLayerData (k := k) r selected where
  rank := r
  moduleCarrier := ModuleCarrier (k := k) r
  localRing := fun v => LocalRing (k := k) v
  localField := fun v => LocalField (k := k) v
  localization := localization (k := k) r
  determinantCarrier := DeterminantCarrier (k := k)
  determinantLocalization := fun v => determinantLocalization (k := k) v
  localLogVolume := localLogVolume (k := k)
  logVolume := logVolume (k := k) selected

theorem actualPaperOModuleLayerData_rank (r : Nat)
    (selected : Finset (NumberField.FinitePlace k)) :
    (actualPaperOModuleLayerData (k := k) r selected).rank = r := rfl

theorem actualPaperOModuleLayerData_moduleCarrier (r : Nat)
    (selected : Finset (NumberField.FinitePlace k)) :
    (actualPaperOModuleLayerData (k := k) r selected).moduleCarrier =
      ModuleCarrier (k := k) r := rfl

theorem actualPaperOModuleLayerData_localRing (r : Nat)
    (selected : Finset (NumberField.FinitePlace k))
    (v : NumberField.FinitePlace k) :
    (actualPaperOModuleLayerData (k := k) r selected).localRing v =
      LocalRing (k := k) v := rfl

theorem localization_add (r : Nat) (v : NumberField.FinitePlace k)
    (s t : ModuleCarrier (k := k) r) :
    localization (k := k) r v (s + t) =
      localization (k := k) r v s + localization (k := k) r v t := by
  simp [localization, Finset.sum_add_distrib]

theorem localization_smul (r : Nat) (v : NumberField.FinitePlace k)
    (a : GlobalRing k) (s : ModuleCarrier (k := k) r) :
    localization (k := k) r v (a • s) =
      completionAlg (k := k) v a * localization (k := k) r v s := by
  simp [localization, Finset.mul_sum, map_mul]


theorem actualPaperOModuleLayerData_determinantCarrier (r : Nat)
    (selected : Finset (NumberField.FinitePlace k)) :
    (actualPaperOModuleLayerData (k := k) r selected).determinantCarrier =
      DeterminantCarrier (k := k) := rfl

theorem determinantLocalization_one (v : NumberField.FinitePlace k) :
    determinantLocalization (k := k) v 1 = 1 :=
  map_one (determinantLocalization (k := k) v)

theorem determinantLocalization_mul (v : NumberField.FinitePlace k)
    (a b : DeterminantCarrier (k := k)) :
    determinantLocalization (k := k) v (a * b) =
      determinantLocalization (k := k) v a * determinantLocalization (k := k) v b :=
  map_mul (determinantLocalization (k := k) v) a b

theorem moduleCarrier_free (r : Nat) :
    Module.Free (GlobalRing k) (ModuleCarrier (k := k) r) :=
  inferInstance

theorem localValuation_mul (v : NumberField.FinitePlace k)
    (x y : LocalField (k := k) v)
    (hx : Valued.v x ≠ 0) (hy : Valued.v y ≠ 0) :
    localValuation (k := k) v (x * y) =
      localValuation (k := k) v x + localValuation (k := k) v y := by
  unfold localValuation
  rw [map_mul, WithZero.log_mul hx hy]


theorem localValuation_one (v : NumberField.FinitePlace k) :
    localValuation (k := k) v 1 = 0 := by
  unfold localValuation
  simp

theorem localLogVolume_one (v : NumberField.FinitePlace k) :
    localLogVolume (k := k) v 1 = 0 := by
  simp [localLogVolume, localValuation]

theorem logVolume_one (selected : Finset (NumberField.FinitePlace k)) :
    logVolume (k := k) selected 1 = 0 := by
  simp [logVolume, localLogVolume_one]

/-- The actual one-column structure from number-field completions. -/
abbrev actualOneColumnStructure :=
  Theorem311Source.sourceOneColumnStructureOfNumberField k

/-- The actual arithmetic vector bundle over the actual one-column structure. -/
def actualArithmeticVectorBundle (r : Nat) :
    Theorem311Source.SourceArithmeticVectorBundle
      (actualOneColumnStructure (k := k)) where
  total := ModuleCarrier (k := k) r
  localization := fun v s => localization (k := k) r v s

theorem actualArithmeticVectorBundle_localization (r : Nat)
    (v : NumberField.FinitePlace k) (s : ModuleCarrier (k := k) r) :
    (actualArithmeticVectorBundle (k := k) r).localization v s =
      localization (k := k) r v s := rfl

end PaperOModuleLayer

end LeanFormal.IUT

end