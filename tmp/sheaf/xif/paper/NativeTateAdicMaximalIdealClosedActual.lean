import tmp.sheaf.xif.paper.NativeTateQSquaresBasicIntegrality
import Mathlib.RingTheory.DiscreteValuationRing.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! # Maximal ideal of the adic completion integers is closed -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeTateAdicMaximalIdealClosedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.NativeTateQSquaresBasicIntegrality
open IsDedekindDomain.HeightOneSpectrum

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

abbrev K := localField (l := l) T b
abbrev R := localRing (l := l) T b

noncomputable def maximalIdealKSet : Set (localField (l := l) T b) :=
  {x | ∃ y : localRing (l := l) T b, y ∈ IsLocalRing.maximalIdeal (localRing (l := l) T b) ∧
    (y : localField (l := l) T b) = x}

noncomputable def uniformizer : localRing (l := l) T b :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible
    (R := localRing (l := l) T b))

theorem uniformizer_irreducible :
    Irreducible (uniformizer (l := l) T b) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible
    (R := localRing (l := l) T b))

theorem uniformizer_valuation_lt_one :
    Valued.v (uniformizer (l := l) T b : localField (l := l) T b) < 1 := by
  letI : Valued (localField (l := l) T b) (WithZero (Multiplicative ℤ)) := inferInstance
  letI : Algebra (localRing (l := l) T b) (localField (l := l) T b) := inferInstance
  have hv := Valuation.valuationSubring.integers
    (v := Valued.v)
  have hle : Valued.v (uniformizer (l := l) T b : localField (l := l) T b) ≤ 1 :=
    hv.map_le_one (uniformizer (l := l) T b)
  have hne : Valued.v (uniformizer (l := l) T b : localField (l := l) T b) ≠ 1 :=
    (mt hv.isUnit_iff_valuation_eq_one.mpr
      (uniformizer_irreducible (l := l) T b).not_isUnit)
  exact lt_of_le_of_ne hle hne

theorem maximalIdeal_eq_setOf_le_uniformizer :
    (IsLocalRing.maximalIdeal (localRing (l := l) T b) : Set (localRing (l := l) T b)) =
      {y : localRing (l := l) T b |
        Valued.v (y : localField (l := l) T b) ≤
          Valued.v (uniformizer (l := l) T b : localField (l := l) T b)} := by
  letI : Valued (localField (l := l) T b) (WithZero (Multiplicative ℤ)) := inferInstance
  letI : Algebra (localRing (l := l) T b) (localField (l := l) T b) := inferInstance
  exact Valuation.Integers.maximalIdeal_eq_setOf_le_v_algebraMap
    (v := Valued.v)
    (O := localRing (l := l) T b)
    (Valuation.valuationSubring.integers
      (v := Valued.v))
    (uniformizer_irreducible (l := l) T b)

theorem maximalIdealKSet_isClosed :
    IsClosed (maximalIdealKSet (l := l) T b) := by
  letI : Valued (localField (l := l) T b) (WithZero (Multiplicative ℤ)) := inferInstance
  letI : Algebra (localRing (l := l) T b) (localField (l := l) T b) := inferInstance
  let r := Valued.v (uniformizer (l := l) T b : localField (l := l) T b)
  have hball : IsClosed {x : localField (l := l) T b | Valued.v x ≤ r} :=
    Valued.isClosed_closedBall (R := localField (l := l) T b) (r := r)
  have hset : maximalIdealKSet (l := l) T b =
      {x : localField (l := l) T b | Valued.v x ≤ r} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Set.ext_iff.mp
        (maximalIdeal_eq_setOf_le_uniformizer (l := l) T b) y).mp hy
    · intro hx
      have hrlt := uniformizer_valuation_lt_one (l := l) T b
      have hxle : Valued.v x ≤ 1 := le_trans hx (le_of_lt hrlt)
      have hxmem : x ∈ localRing (l := l) T b :=
        (mem_adicCompletionIntegers
          (R := NumberField.RingOfIntegers T.arithmetic.F)
          (K := T.arithmetic.F)
          (v := localPrime (l := l) T b)).mpr hxle
      refine ⟨⟨x, hxmem⟩, ?_, rfl⟩
      exact (Set.ext_iff.mp
        (maximalIdeal_eq_setOf_le_uniformizer (l := l) T b) ⟨x, hxmem⟩).mpr hx
  rw [hset]
  exact hball

end LeanFormal.IUT.XiFPaper.NativeTateAdicMaximalIdealClosedActual

end
