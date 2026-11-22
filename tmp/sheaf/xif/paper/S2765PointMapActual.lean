import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2765PointMapActual

open LeanFormal.IUT
open NumberField
open NumberField.InfinitePlace

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The actual rational point map into the mixed space: a rational number is
mapped to K by `algebraMap ℚ K`, then to the mixed space by the actual mixed
embedding. -/
noncomputable def abcPointToMixedSpace (x : ℚ) :
    NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.mixedEmbedding K (algebraMap ℚ K x)

@[simp] theorem abcPointToMixedSpace_apply (x : ℚ) :
    abcPointToMixedSpace K x =
      NumberField.mixedEmbedding K (algebraMap ℚ K x) := rfl

theorem abcPointToMixedSpace_abcRationalPoint (a c : Nat) :
    abcPointToMixedSpace K (abcRationalPoint a c) =
      NumberField.mixedEmbedding K
        (algebraMap ℚ K (abcRationalPoint a c)) := rfl

@[simp] theorem abcPointToMixedSpace_isReal
    (x : ℚ) (w : {w : InfinitePlace K // IsReal w}) :
    (abcPointToMixedSpace K x).1 w =
      embedding_of_isReal w.prop (algebraMap ℚ K x) := by
  simp [abcPointToMixedSpace, NumberField.mixedEmbedding]

@[simp] theorem abcPointToMixedSpace_isComplex
    (x : ℚ) (w : {w : InfinitePlace K // IsComplex w}) :
    (abcPointToMixedSpace K x).2 w =
      w.val.embedding (algebraMap ℚ K x) := by
  simp [abcPointToMixedSpace, NumberField.mixedEmbedding]

/-- The map is the actual mixed embedding of the rational point, so the bridge
log-shell point candidate is `abcPointToMixedSpace K (abcRationalPoint a c)`. -/
theorem abcPointToMixedSpace_eq_mixedEmbedding (a c : Nat) :
    abcPointToMixedSpace K (abcRationalPoint a c) =
      NumberField.mixedEmbedding K
        (algebraMap ℚ K (abcRationalPoint a c)) := rfl

#check abcPointToMixedSpace
#check abcPointToMixedSpace_apply
#check abcPointToMixedSpace_abcRationalPoint
#check abcPointToMixedSpace_isReal
#check abcPointToMixedSpace_isComplex
#print axioms abcPointToMixedSpace_abcRationalPoint

end LeanFormal.IUT.XiFPaper.S2765PointMapActual
end
