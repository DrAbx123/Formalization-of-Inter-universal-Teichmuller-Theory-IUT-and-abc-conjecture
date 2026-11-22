import tmp.sheaf.xif.paper.S2147PaperIntegralClosureOUnitsActionActual
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # S2163: nontriviality of the integral-closure O^× Galois action

The action of S2147 is genuine.  Nontriviality is reduced to an explicit
cyclotomic witness: a root of unity `ζ` of order `n > 0` in the integral closure
and a local Galois automorphism `σ` with `σ ζ ≠ ζ`.  Such a witness gives an
integral unit moved by the action.  The existence of this witness is the exact
missing datum; no σ or ζ is fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2163IntegralClosureNontrivialActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Explicit cyclotomic datum: a root of unity in the integral closure and a
local Galois automorphism moving it. -/
structure S2163CyclotomicNontrivialWitness where
  n : Nat
  hn : 0 < n
  ζ : S2147PaperIntegralClosure T b
  hζ : IsPrimitiveRoot ζ n
  σ : S2147PaperIntegralClosureGaloisGroup T b
  hσ : σ ζ ≠ ζ

/-- A root of unity is an integral unit. -/
theorem s2163_rootOfUnity_mem_integers
    {n : Nat} (hn : 0 < n) {ζ : S2147PaperIntegralClosure T b}
    (hζ : IsPrimitiveRoot ζ n) :
    ζ ∈ Integers (S2147PaperIntegralClosure T b) := by
  rw [mem_integers_iff]
  have hnorm : ‖ζ‖ = 1 := by
    have hpow : ‖ζ‖ ^ n = 1 := by
      rw [← norm_pow, hζ.pow_eq_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hn.ne').mp hpow
  simpa [hnorm] using zero_le_one

/-- The integral unit attached to a root of unity. -/
noncomputable def s2163UnitOfRoot
    {n : Nat} (hn : 0 < n)
    (ζ : S2147PaperIntegralClosure T b)
    (hζ : IsPrimitiveRoot ζ n) :
    S2147PaperIntegralClosureOUnits T b :=
  let x : Integers (S2147PaperIntegralClosure T b) :=
    ⟨ζ, s2163_rootOfUnity_mem_integers T b hn hζ⟩
  have hxpow : x ^ n = 1 := Subtype.ext (by simpa using hζ.pow_eq_one)
  Units.ofPowEqOne x n hxpow hn.ne'

/-- The integral unit attached to a cyclotomic witness. -/
noncomputable def s2163WitnessUnit
    (W : S2163CyclotomicNontrivialWitness T b) :
    S2147PaperIntegralClosureOUnits T b :=
  s2163UnitOfRoot T b W.hn W.ζ W.hζ

/-- The action sends the unit of `ζ` to the unit of `σ ζ`. -/
theorem s2163UnitOfRoot_action
    (W : S2163CyclotomicNontrivialWitness T b) :
    s2147PaperIntegralClosureOUnitsGaloisAction T b W.σ
        (s2163UnitOfRoot T b W.hn W.ζ W.hζ) =
      s2163UnitOfRoot T b W.hn (W.σ W.ζ)
        (W.hζ.map_of_injective W.σ.injective) := by
  apply Units.ext
  rfl

/-- The cyclotomic witness gives a genuinely moved integral unit. -/
theorem s2163WitnessUnit_moved
    (W : S2163CyclotomicNontrivialWitness T b) :
    s2147PaperIntegralClosureOUnitsGaloisAction T b W.σ
        (s2163WitnessUnit T b W) ≠ s2163WitnessUnit T b W := by
  rw [s2163WitnessUnit, s2163UnitOfRoot_action]
  intro h
  apply W.hσ
  have hval := congrArg
    (fun u : S2147PaperIntegralClosureOUnits T b =>
      ((u : Integers (S2147PaperIntegralClosure T b)) :
        S2147PaperIntegralClosure T b)) h
  simpa [s2163UnitOfRoot, Units.val_ofPowEqOne] using hval

/-- Consequently the S2147 nontrivial-action obligation is discharged by any
cyclotomic witness. -/
theorem s2163NontrivialAction_of_witness
    (W : S2163CyclotomicNontrivialWitness T b) :
    S2147IntegralClosureNontrivialActionRequired T b :=
  ⟨W.σ, s2163WitnessUnit T b W, s2163WitnessUnit_moved T b W⟩

/-- Exact missing datum: existence of the cyclotomic witness. -/
def S2163CyclotomicNontrivialWitnessRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (S2163CyclotomicNontrivialWitness T b)

#check S2163CyclotomicNontrivialWitness
#check s2163_rootOfUnity_mem_integers
#check s2163WitnessUnit
#check s2163WitnessUnit_moved
#check s2163NontrivialAction_of_witness
#check S2163CyclotomicNontrivialWitnessRequired

end LeanFormal.IUT.XiFPaper.S2163IntegralClosureNontrivialActual
end
