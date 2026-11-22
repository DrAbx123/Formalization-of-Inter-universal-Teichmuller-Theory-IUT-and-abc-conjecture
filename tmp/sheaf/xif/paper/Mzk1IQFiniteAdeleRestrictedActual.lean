import tmp.sheaf.xif.paper.Mzk1RestrictedProductReuseActual
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Tactic

/-! # B#2: real-place/index/integer restricted product data for IQ

Indexes are the actual HeightOneSpectrum of the ring of integers; local fields are
the actual adic completions; integer references are the actual adicCompletionIntegers.

No FLT import is needed for this skeleton.  The eventual-integrality condition is
proved from the Mathlib restricted-product subtype field.
-/

noncomputable section
open scoped RestrictedProduct
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1IQFiniteAdeleRestrictedActual

open LeanFormal.IUT.XiFPaper.Mzk1RestrictedProductReuseActual
open IsDedekindDomain

variable (K : Type) [Field K] [NumberField K]

/-- Actual index: finite places of K (height-one primes of the integer ring). -/
abbrev iqPlaceIndex (K : Type) [Field K] [NumberField K] : Type :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

/-- Actual local field at an index. -/
abbrev iqLocalField (K : Type) [Field K] [NumberField K]
    (i : iqPlaceIndex K) : Type := i.adicCompletion K

/-- Actual integer reference at an index. -/
abbrev iqLocalIntegers (K : Type) [Field K] [NumberField K]
    (i : iqPlaceIndex K) : Set (iqLocalField K i) :=
  (i.adicCompletionIntegers K : Set (i.adicCompletion K))

/-- The actual-place restricted product carrier. -/
abbrev IQFiniteAdeleProductCarrier (K : Type) [Field K] [NumberField K] : Type :=
  IQRestrictedProductCarrier (iqPlaceIndex K) (iqLocalField K) (iqLocalIntegers K)

/-- Coordinate map out of the true-place carrier. -/
def iqCoordinateMap (x : IQFiniteAdeleProductCarrier K) :
    (i : iqPlaceIndex K) → iqLocalField K i :=
  fun i => x.1 i

/-- Every coordinate eventually lies in the actual integer ring. -/
theorem iqCoordinateMap_eventually_mem_integers
    (x : IQFiniteAdeleProductCarrier K) :
    ∀ᶠ i in Filter.cofinite, iqCoordinateMap K x i ∈ iqLocalIntegers K i :=
  x.2

/-- The same statement with the coercion field. -/
theorem iqCarrier_coe_mem_integers
    (x : IQFiniteAdeleProductCarrier K) :
    ∀ᶠ i in Filter.cofinite, x.1 i ∈ iqLocalIntegers K i :=
  x.2

/-- Compatibility with the abstract Mathlib restricted product (rfl). -/
theorem iqCarrier_eq_mathlib_restrictedProduct :
    IQFiniteAdeleProductCarrier K =
      (Πʳ i : iqPlaceIndex K, [iqLocalField K i, iqLocalIntegers K i]) := rfl

/-- Coordinate map is injective (the carrier is a subtype of the full product). -/
theorem iqCoordinateMap_injective :
    Function.Injective (iqCoordinateMap K) := by
  intro x y h
  exact Subtype.ext (funext fun i => congrFun h i)

#check iqPlaceIndex
#check iqLocalField
#check iqLocalIntegers
#check IQFiniteAdeleProductCarrier
#check iqCoordinateMap
#check iqCoordinateMap_eventually_mem_integers
#check iqCarrier_eq_mathlib_restrictedProduct
#check iqCoordinateMap_injective

/-- Definition-level identification with Mathlib's finite adele ring. -/
theorem iqCarrier_eq_mathlibFiniteAdeleRing (K : Type) [Field K] [NumberField K] :
    IQFiniteAdeleProductCarrier K =
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K := rfl

/-- CommRing structure transported along the definition-level identification. -/
noncomputable instance iqCommRing (K : Type) [Field K] [NumberField K] :
    CommRing (IQFiniteAdeleProductCarrier K) :=
  inferInstanceAs (CommRing
    (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K))

/-- TopologicalSpace structure transported along the identification. -/
noncomputable instance iqTopologicalSpace (K : Type) [Field K] [NumberField K] :
    TopologicalSpace (IQFiniteAdeleProductCarrier K) :=
  inferInstanceAs (TopologicalSpace
    (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K))

/-- K-algebra structure transported along the identification. -/
noncomputable instance iqAlgebra (K : Type) [Field K] [NumberField K] :
    Algebra K (IQFiniteAdeleProductCarrier K) :=
  inferInstanceAs (Algebra K
    (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K))

/-- IsTopologicalRing structure transported along the identification. -/
noncomputable instance iqIsTopologicalRing (K : Type) [Field K] [NumberField K] :
    IsTopologicalRing (IQFiniteAdeleProductCarrier K) :=
  inferInstanceAs (IsTopologicalRing
    (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K))

/-- Ring equivalence from the carrier to Mathlib's finite adele ring. -/
noncomputable def iqFiniteAdeleRingEquiv (K : Type) [Field K] [NumberField K] :
    IQFiniteAdeleProductCarrier K ≃+*
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K :=
  RingEquiv.refl _

#check iqCarrier_eq_mathlibFiniteAdeleRing
#check iqFiniteAdeleRingEquiv
#check iqCommRing
#check iqTopologicalSpace
#check iqAlgebra
#check iqIsTopologicalRing

end LeanFormal.IUT.XiFPaper.Mzk1IQFiniteAdeleRestrictedActual
end
