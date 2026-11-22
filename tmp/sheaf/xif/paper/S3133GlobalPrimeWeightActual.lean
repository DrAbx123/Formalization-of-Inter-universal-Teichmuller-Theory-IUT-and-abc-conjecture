import tmp.sheaf.xif.paper.S3133ValueGroupDegreeActual

/-!
# Strict positivity of the actual global prime weight (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: abc task-39 degree-faithful
value-group action (needs an actual prime index v with globalPrimeWeight v ≠ 0);
S3133ValueGroupDegreeActual degree faithfulness.

Source: IUT III, Definition 3.8, (i), p. 112-113 (q-pilot data at V_bad);
IUT III, Remark 3.1.1, (ii), p. 95-97 (completion-degree normalization);
[AbsTopIII], Proposition 5.8, (ii) (realified degree nondegeneracy).

The actual realified arithmetic weight of a global prime place is
globalPrimeWeight (finite p) = log |Norm(p)| at finite places and 1 at infinite
places.  At finite places |Norm(p)| > 1, so the weight is strictly positive; at
infinite places it is 1.  Hence EVERY actual global prime index is a valid
nonzero-weight generator (no choice of generator is needed), and the
Real-indexed generator homomorphism of S3133ValueGroupDegreeActual is
degree-faithful unconditionally.

No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133GlobalPrimeWeightActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- Every actual global prime weight is strictly positive. -/
theorem globalPrimeWeight_pos (v : GlobalPrimeIndex (X := X)) :
    0 < globalPrimeWeight (X := X) v := by
  cases v with
  | finite p =>
      unfold globalPrimeWeight
      exact Real.log_pos (by
        exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p.maximalIdeal)
  | infinite w =>
      unfold globalPrimeWeight
      norm_num

/-- Every actual global prime weight is nonzero: any global prime index is a
valid nonzero-weight value-group generator. -/
theorem globalPrimeWeight_ne_zero (v : GlobalPrimeIndex (X := X)) :
    globalPrimeWeight (X := X) v ≠ 0 :=
  ne_of_gt (globalPrimeWeight_pos X v)

/-- Unconditional degree faithfulness of the Real-indexed generator on ANY actual
global prime index: the degree kernel is trivial. -/
theorem globalRealifiedPrimePowerHom_degree_faithful_unconditional
    (v : GlobalPrimeIndex (X := X)) (r s : Multiplicative Real)
    (h : globalDegree (X := X) (globalRealifiedPrimePowerHom X v r) =
      globalDegree (X := X) (globalRealifiedPrimePowerHom X v s)) :
    r = s :=
  globalRealifiedPrimePowerHom_degree_faithful X v
    (globalPrimeWeight_ne_zero X v) r s h

end LeanFormal.IUT.XiFPaper.S3133GlobalPrimeWeightActual
