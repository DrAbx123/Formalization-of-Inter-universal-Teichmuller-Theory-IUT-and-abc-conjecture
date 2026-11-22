import tmp.sheaf.xif.paper.S2174CyclotomicWitnessActual

/-! # S2184: exact minpoly-degree API gap for the Galois move

S2174 constructs the actual primitive root `s2174PrimitiveRoot T b n hn`.
A local Galois automorphism moving it can be produced from a second root of its
minimal polynomial, equivalently from `2 ≤ natDegree (minpoly K ζ)`.  The tree
currently has no proof of this degree bound for the constructed root, and no
transport of the S2046 cyclotomic character to `SourceAlgebraicClosure`.
This file records the exact API gap without fabricating a σ. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2184GaloisMoveActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual
open LeanFormal.IUT.XiFPaper.S2174CyclotomicWitnessActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The exact degree bound needed for the constructed primitive root. -/
def S2184PrimitiveRootDegreeRequired
    (n : Nat) (hn : 0 < n) : Prop :=
  2 ≤ (minpoly (NormalizedCompletion (sectionKPlace T b))
    (s2174PrimitiveRoot T b n hn)).natDegree

/-- The equivalent non-membership form. -/
def S2184PrimitiveRootNotInBaseRequired
    (n : Nat) (hn : 0 < n) : Prop :=
  s2174PrimitiveRoot T b n hn ∉
    (algebraMap (NormalizedCompletion (sectionKPlace T b))
      (S2147PaperIntegralClosure T b)).range

theorem s2184_degree_iff_notInBase
    (n : Nat) (hn : 0 < n)
    (hint : IsIntegral (NormalizedCompletion (sectionKPlace T b))
      (s2174PrimitiveRoot T b n hn)) :
    S2184PrimitiveRootDegreeRequired T b n hn ↔
      S2184PrimitiveRootNotInBaseRequired T b n hn :=
  minpoly.two_le_natDegree_iff hint

/-- Exact missing transport/API: the actual primitive root is not fixed by the
local Galois group, or equivalently its minimal polynomial has degree at least
two.  No witness is asserted. -/
structure S2184GaloisMoveAPIRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  n : Nat
  hn : 0 < n
  notInBase : S2184PrimitiveRootNotInBaseRequired T b n hn

def S2184GaloisMoveAPIRequiredProp
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (S2184GaloisMoveAPIRequired T b)

#check S2184PrimitiveRootDegreeRequired
#check S2184PrimitiveRootNotInBaseRequired
#check s2184_degree_iff_notInBase
#check S2184GaloisMoveAPIRequired
#check S2184GaloisMoveAPIRequiredProp

end LeanFormal.IUT.XiFPaper.S2184GaloisMoveActual
end
