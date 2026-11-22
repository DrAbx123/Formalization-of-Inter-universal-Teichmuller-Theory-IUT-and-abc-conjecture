import tmp.sheaf.xif.paper.Mzk1PaperLabelProjectionActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic

/-! # B#2 semantic: Bad index -> rational prime actual bridge

The actual bad index b maps to the K-place nativeBadToKPlace T b; taking the
underlying rational prime ideal and its absolute norm gives an actual function
  badRationalPrime : Bad (nativePlaceSelection T) -> Nat.

Exact obstacle: this is a residue-prime projection, not the paper theta-label
map.  A canonical Bad -> ProcessionLabel l map is not present in T.arithmetic;
the only available place-level route is via the chosen lift nativeBadToKPlace
(and its base/underlying rational prime), which is not a theta label.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperLabelBadIndexBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperLabelProjectionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual rational prime attached to a bad index through the chosen K-place lift. -/
noncomputable def badRationalPrime (b : Bad (nativePlaceSelection T)) : Nat :=
  rationalPrimeOfFinitePlace (K := T.arithmetic.K) ((nativeBadToKPlace T b).maximalIdeal)

/-- Definitional form: norm of the underlying rational prime ideal. -/
theorem badRationalPrime_eq (b : Bad (nativePlaceSelection T)) :
    badRationalPrime T b =
      Ideal.absNorm (((nativeBadToKPlace T b).maximalIdeal.asIdeal).under Int) := rfl

/-- The bad index does give an actual function to Nat (via the K-place lift). -/
theorem badRationalPrime_function :
    ∃ f : Bad (nativePlaceSelection T) → Nat,
      ∀ b, f b = badRationalPrime T b :=
  ⟨badRationalPrime T, fun _ => rfl⟩

/-- Named interface: a Bad-indexed theta-label projection.  No canonical
T.arithmetic map to ProcessionLabel is available. -/
structure BadThetaLabelMap (l : PrimeGeFive) where
  labelOf : Bad (nativePlaceSelection T) → PaperLabelGroup l

#check badRationalPrime
#check badRationalPrime_eq
#check badRationalPrime_function
#check BadThetaLabelMap
end LeanFormal.IUT.XiFPaper.Mzk1PaperLabelBadIndexBridgeActual
end
