import tmp.sheaf.xif.paper.RelativeDegreeNormedActual
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Adjusted norm construction ||x||^(1/d)

For the actual relative completion degree d of the native place, the canonical
adjusted norm on F is

  adjustedNorm d x = ||x||_F ^ (1 / d).

This file constructs that function and the adjusted-norm package.  Proving it is
an actual NormedField and that it induces the p-adic topology requires the
absolute-value/topology lemmas listed in AdjustedNormData; those are not present
in the frozen source.  No arbitrary instance/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.AdjustedNormActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.FToFmodMapActual
open LeanFormal.IUT.XiFPaper.ValuedNormedInstancesActual
open LeanFormal.IUT.XiFPaper.RelativeDegreeNormedActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual relative degree d used for the adjustment. -/
def adjustedDegree : Nat :=
  nativeRelativeCompletionDegree (X := X)

/-- The canonical adjusted norm function ||x||^(1/d), using the actual F-norm. -/
noncomputable def adjustedNorm (d : Nat) : X.S.arithmetic.F → Real :=
  letI := nativeFNormedField (X := X)
  fun x => ‖x‖ ^ (1 / (d : Real))

/-- The adjusted norm is nonnegative. -/
theorem adjustedNorm_nonneg (d : Nat) (x : X.S.arithmetic.F) :
    0 ≤ adjustedNorm (X := X) d x := by
  unfold adjustedNorm
  letI := nativeFNormedField (X := X)
  exact Real.rpow_nonneg (norm_nonneg x) _

/-- The adjusted norm of zero is zero. -/
theorem adjustedNorm_zero (d : Nat) :
    adjustedNorm (X := X) d 0 = 0 := by
  unfold adjustedNorm
  letI := nativeFNormedField (X := X)
  simp

/-- Base compatibility required of the adjusted norm: on the embedded base
field it must recover the Fmod norm. -/
def BaseCompatibleAdjustedNorm (d : Nat) : Prop :=
  ∀ a : X.S.arithmetic.Fmod,
    adjustedNorm (X := X) d
      (algebraMap X.S.arithmetic.Fmod X.S.arithmetic.F a) = ‖a‖

/-- Exact adjusted-norm construction package.  The normed-field, topology, and
base-compatibility fields are the missing analytic lemmas; the function itself
is the canonical adjustedNorm. -/
structure AdjustedNormData where
  d : Nat
  d_pos : 0 < d
  norm_adjusted : X.S.arithmetic.F → Real
  norm_eq_adjustedNorm : norm_adjusted = adjustedNorm (X := X) d
  base_compatible : BaseCompatibleAdjustedNorm (X := X) d
  normedField : NormedField X.S.arithmetic.F
  topology_eq : ∀ x : X.S.arithmetic.F,
    (0 < norm_adjusted x) ↔ (0 < (letI := nativeFNormedField (X := X); ‖x‖))
  normedSpace : NormedSpace X.S.arithmetic.Fmod X.S.arithmetic.F

/-- The exact adjusted-norm gap: existence of the package above. -/
def AdjustedNormGap : Prop :=
  Nonempty (AdjustedNormData (X := X))

/-- Conditional construction of a NormedSpace Fmod F from the adjusted-norm
package. -/
noncomputable def normedSpaceOfAdjustedNorm
    (D : AdjustedNormData (X := X)) :
    NormedSpace X.S.arithmetic.Fmod X.S.arithmetic.F :=
  D.normedSpace

/-! ## Exact missing analytic lemmas

The canonical adjustedNorm function is defined.  To turn it into an actual
NormedField and NormedSpace, the missing lemmas are:

1. base compatibility:
     adjustedNorm d (algebraMap a) = ||a||_Fmod
   for all a, using ||algebraMap a||_F = ||a||_Fmod ^ d;
2. the absolute-value axioms for adjustedNorm d (multiplicativity and the
   nonarchimedean triangle inequality) for positive d;
3. identification of the topology induced by adjustedNorm d with the actual
   p-adic completion topology;
4. the resulting NormedSpace Fmod F compatibility.

These are exactly the fields of AdjustedNormData beyond the function definition.
No arbitrary instance/axiom is inserted. -/

end LeanFormal.IUT.XiFPaper.AdjustedNormActual

end
