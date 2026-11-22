import tmp.sheaf.xif.paper.S2163IntegralClosureNontrivialActual
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # S2174: actual primitive roots of unity in the integral closure

Constructs a primitive `n`-th root of unity in the actual normed algebraic
closure at the paper K-place, for every `n > 0`.  The remaining gap to the S2163
nontrivial Galois witness is a local Galois automorphism moving such a root; this
is recorded as an exact missing structure, not fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2174CyclotomicWitnessActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual
open LeanFormal.IUT.XiFPaper.S2163IntegralClosureNontrivialActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- An actual primitive `n`-th root of unity in the normed algebraic closure
of the paper K-place. -/
noncomputable def s2174PrimitiveRoot
    (n : Nat) (hn : 0 < n) : S2147PaperIntegralClosure T b := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : HasEnoughRootsOfUnity
      (AlgebraicClosure (NormalizedCompletion (sectionKPlace T b))) n :=
    inferInstance
  exact Classical.choose
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure (NormalizedCompletion (sectionKPlace T b))) n)

theorem s2174PrimitiveRoot_spec
    (n : Nat) (hn : 0 < n) :
    IsPrimitiveRoot (s2174PrimitiveRoot T b n hn) n := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : HasEnoughRootsOfUnity
      (AlgebraicClosure (NormalizedCompletion (sectionKPlace T b))) n :=
    inferInstance
  exact Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure (NormalizedCompletion (sectionKPlace T b))) n)

/-- Exact missing datum: a local Galois automorphism moving the actual primitive
root `s2174PrimitiveRoot n hn`. -/
structure S2174GaloisMovesRootRequired
    (n : Nat) (hn : 0 < n) where
  σ : S2147PaperIntegralClosureGaloisGroup T b
  hσ : σ (s2174PrimitiveRoot T b n hn) ≠ s2174PrimitiveRoot T b n hn

/-- Any actual Galois move of the constructed primitive root is a cyclotomic
witness in the sense of S2163. -/
noncomputable def s2174CyclotomicWitnessOfGaloisMove
    (n : Nat) (hn : 0 < n)
    (M : S2174GaloisMovesRootRequired T b n hn) :
    S2163CyclotomicNontrivialWitness T b where
  n := n
  hn := hn
  ζ := s2174PrimitiveRoot T b n hn
  hζ := s2174PrimitiveRoot_spec T b n hn
  σ := M.σ
  hσ := M.hσ

/-- Exact first missing form: there exists `n > 0` and a Galois automorphism
moving the actual primitive root. -/
def S2174GaloisMovesPrimitiveRootRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  ∃ (n : Nat) (hn : 0 < n), Nonempty (S2174GaloisMovesRootRequired T b n hn)

#check s2174PrimitiveRoot
#check s2174PrimitiveRoot_spec
#check S2174GaloisMovesRootRequired
#check s2174CyclotomicWitnessOfGaloisMove
#check S2174GaloisMovesPrimitiveRootRequired

end LeanFormal.IUT.XiFPaper.S2174CyclotomicWitnessActual
end
