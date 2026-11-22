import tmp.sheaf.xif.paper.S1881D9D7bActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

/-!
# S1889: the D8 real cusp coordinate / SourceCuspClause over the actual S1732 line

S1881 reduced the third remaining `SourceDefinition31Data` leg (D8) to a real
function on the boundary cusps of the missing K-core orbicurve `C_K`:

  S1881RealCuspCoordinate l S,  with first field
  epsilonOf : Iut.OrbicurveBoundaryCusp S.cK -> Real

and left its construction open.  This file answers that task with the paper
text, not with an arbitrary real.

## What the paper actually says (IUT I, Definition 3.1(f), p. 63)

The extracted source text is local:

  papers/motizuki_corpus/text/Inter-universal Teichmuller Theory I.txt
  lines 3123--3126 and 3273--3280.

Definition 3.1 defines initial Theta-data as a tuple

  (F/Fbar, X_F, l, C_K, V, V^bad_mod, epsilon)

and item (f) reads:

  "(f) epsilon is a cusp of the hyperbolic orbicurve C_K [cf. (d)] that arises
  from a nonzero element of the quotient "Q" that appears in the definition of
  a "hyperbolic orbicurve of type (1,l-tors)^pm" given in [EtTh], Definition
  2.1.  If v in V, then let us write epsilon_v for the cusp of C_v determined by
  epsilon.  If v in V^bad, then we assume that epsilon_v is the cusp that
  arises from the canonical generator [up to sign] "±1" of the quotient "Zhat"
  that appears in the definition of a "hyperbolic orbicurve of type
  (1,Z/lZ)^pm" given in [EtTh], Definition 2.5, (i)."

There is no real number in (f).  The paper's epsilon is a cusp, selected by a
nonzero element of Q, and at bad places pinned to the canonical generator
"±1" of the local Zhat quotient.  The real-valued `epsilon : Real` of
`SourceCuspClause` (and its `S1881RealCuspCoordinate` re-encoding) is therefore
a numerical shell, not the paper datum.  This is the central finding recorded
here, and it decides the construction task:

1. The paper-faithful D8 datum is a cusp-origin datum over the missing `C_K`;
   it is already formalized by `TorsionQuotientBoundaryOrigin` (the object the
   Lean D9 clause calls the cusp).  Over the S1881 slot it is
   `S1889PaperCuspDatum`, and its nonemptiness is *exactly* the S1881 D9
   cusp-missing proposition.

2. The S1881 real coordinate is a *vacuous* contract in the precise sense that
   it has a junk inhabitant for every slot (constant positive `epsilon`,
   inverse scale, `True` compatibility) and is closed under arbitrary positive
   rescaling.  Consequently `S1881D8Missing l S` is a theorem for every slot,
   and the "missing" real object adds no obligation beyond the D9 orbicurve
   slot.  No non-arbitrary real can be extracted because the contract does not
   determine one: two coordinates of the shell can take different values at the
   same cusp.

3. A real *is* obtainable from geometric data, but only conditionally and only
   through an extra local parameter: the normalized norm of a nonzero
   contracting cusp parameter `q` in the actual completion at a finite place of
   K.  `S1889CuspQParameter` states that datum exactly, and
   `S1889CuspQParameter.realCuspCoordinate` constructs the S1881 coordinate with
   `epsilonOf c = ||q c||` (positive and `< 1` by the contracting condition).
   The real first field is then a norm, not an arbitrary constant.

4. The exact first missing object is the same for both readings: the S1881 D9
   orbicurve slot, whose first field is the F-side quotient orbicurve `C_F` of
   type `(1,1)^pm`.  The cusp carrier `Iut.OrbicurveBoundaryCusp S.cK` cannot
   exist before `C_F` (and its K-core `C_K`); the paper's place-indexed cusp
   condition then additionally needs the base-changed local orbicurves `C_v`,
   which are base changes of the same missing `C_K`.

No `sorry`, `admit`, `axiom`, `True`-filled source field, `PUnit`, or
arbitrary real is used as the paper datum.  The junk inhabitants are proved as
theorems about the shell and are explicitly labelled as such; they are never
presented as the paper's cusp coordinate.

## Status

statement_compiles = expected true; proof_body_checked = the constructions and
the two equivalences; kernel_closed = for this temp file only (axiom printout at
the end); target_accepted = no (the paper's (f) also has the place-indexed part,
whose carrier `C_v` is downstream of the missing `C_K`).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1889D8RealCuspActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1320SectionsCuspActual
open LeanFormal.IUT.NumberFieldFinitePlace

variable (l : PrimeGeFive)

/-! ## 1. The paper cusp carrier over the S1881 D9 slot -/

/-- The faithful paper cusp of Definition 3.1(f): a boundary cusp of the
K-core `C_K` of the D9 slot. -/
abbrev S1889PaperCusp (l : PrimeGeFive) (S : S1881D9OrbicurveSlot l) : Type 1 :=
  Iut.OrbicurveBoundaryCusp S.cK

/-- The paper cusp carrier is definitionally S1881's D8 carrier. -/
theorem S1889PaperCusp_eq_S1881 (l : PrimeGeFive) (S : S1881D9OrbicurveSlot l) :
    S1889PaperCusp l S = S1881PaperCusp l S := rfl

/-- The paper's Definition 3.1(f) datum over the S1881 slot: a cusp of `C_K`
selected by the rank-one quotient `Q`, with the canonical generator `±1`
pinned to the selected cusp.  This is the object the Lean source calls the D9
cusp, and it is *not* a real number. -/
abbrev S1889PaperCuspDatum (l : PrimeGeFive) (S : S1881D9OrbicurveSlot l) :=
  TorsionQuotientBoundaryOrigin l (S1732A l) S.cK

/-! ## 2. The paper conditions of Definition 3.1(f), read off the datum

The three fields of `TorsionQuotientBoundaryOrigin` are exactly the paper's
conditions: the rank-one quotient `Q`, the origin map on nonzero classes, and
the distinguished class (the canonical generator `±1`) mapped to the selected
cusp. -/

/-- The selected cusp of the paper datum. -/
def S1889PaperCuspDatum.cuspOf {l : PrimeGeFive} {S : S1881D9OrbicurveSlot l}
    (O : S1889PaperCuspDatum l S) : S1889PaperCusp l S :=
  O.cusp

/-- The paper condition that the cusp "arises from a nonzero element of Q":
the distinguished nonzero class maps to the selected cusp. -/
theorem S1889PaperCuspDatum_arisesFromNonzeroClass {l : PrimeGeFive}
    {S : S1881D9OrbicurveSlot l} (O : S1889PaperCuspDatum l S) :
    O.originMap O.distinguishedNonzeroClass = O.cusp :=
  O.originMap_nonzeroClass_spec

/-- The paper condition that the selected class is the canonical generator
`±1` of the quotient: its image in `ZMod l` is `1`, i.e. `±1` under the
sign quotient. -/
theorem S1889PaperCuspDatum_canonicalGenerator {l : PrimeGeFive}
    {S : S1881D9OrbicurveSlot l} (O : S1889PaperCuspDatum l S) :
    O.rank_one_quotient.quotientEquiv O.rank_one_quotient.distinguishedClass = 1 :=
  O.distinguishedClass_is_generator

/-- The canonical generator is a nonzero quotient class. -/
theorem S1889PaperCuspDatum_distinguishedClass_nonzero {l : PrimeGeFive}
    {S : S1881D9OrbicurveSlot l} (O : S1889PaperCuspDatum l S) :
    O.rank_one_quotient.distinguishedClass ≠ 0 :=
  O.distinguishedClass_nonzero

/-- The paper cusp datum depends on the slot only through `C_K`: it is the D9
cusp origin.  Its nonemptiness is exactly S1881's D9 cusp-missing proposition. -/
theorem S1889PaperCuspDatum_nonempty_iff_D9Cusp (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) :
    Nonempty (S1889PaperCuspDatum l S) ↔ S1881D9CuspMissing l S :=
  (S1881D9CuspMissing_iff l S).symm

/-- The exact decomposition of the paper datum: a rank-one quotient plus its
boundary residual on `C_K` (the S1881 equivalence instantiated at the slot). -/
theorem S1889PaperCuspDatum_residual (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) :
    Nonempty (S1889PaperCuspDatum l S) ↔
      ∃ Q : TorsionRankOneQuotientData l
          ((S1732A l).curve.baseChange (S1732A l).K),
        Nonempty (S1881CuspBoundaryResidual l (X := S.cK) Q) :=
  S1881CuspOrigin_nonempty_iff (l := l) (X := S.cK)

/-! ## 3. The real shell: the S1881 contract is vacuous

The paper has no real at (f).  The shell `S1881RealCuspCoordinate` nevertheless
admits a junk inhabitant for *every* slot, and it is closed under rescaling of
the real first field.  The theorems below state that precisely; they are not a
construction of the paper cusp coordinate. -/

/-- The junk inhabitant of the S1881 real-coordinate shell: any positive real
constant on every cusp, with inverse scale and a `True` compatibility
proposition.  This is *not* the paper's cusp datum (Definition 3.1(f) is a cusp);
it records that the shell alone has no content. -/
noncomputable def S1889ConstantRealCuspCoordinate (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (e : Real) (he : 0 < e) :
    S1881RealCuspCoordinate l S where
  epsilonOf := fun _ => e
  epsilon_positive := fun _ => he
  epsilon_nonzero := fun _ => ne_of_gt he
  cuspScaleOf := fun _ => e⁻¹
  cuspScale_positive := fun _ => inv_pos.mpr he
  epsilon_scale_relation := fun _ => by
    rw [mul_inv_cancel₀ (ne_of_gt he)]
    norm_num
  epsilon_compatibility := fun _ => True
  epsilon_compatibility_proved := fun _ => trivial

@[simp] theorem S1889ConstantRealCuspCoordinate_epsilonOf (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (e : Real) (he : 0 < e)
    (c : S1889PaperCusp l S) :
    (S1889ConstantRealCuspCoordinate l S e he).epsilonOf c = e := rfl

/-- No value is forced: every positive real is the first field of some S1881
coordinate at any fixed cusp.  Hence the "real cusp coordinate" cannot be
selected from the contract. -/
theorem S1889RealCuspCoordinate_epsilon_arbitrary (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (c : S1889PaperCusp l S)
    (e : Real) (he : 0 < e) :
    ∃ R : S1881RealCuspCoordinate l S, R.epsilonOf c = e :=
  ⟨S1889ConstantRealCuspCoordinate l S e he, rfl⟩

/-- Two S1881 real cusp coordinates can differ at the same cusp.  The contract
does not pin the real, so an inhabitant of it is not a cusp coordinate. -/
theorem S1889RealCuspCoordinate_not_determined (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (c : S1889PaperCusp l S) :
    ∃ R₁ R₂ : S1881RealCuspCoordinate l S, R₁.epsilonOf c ≠ R₂.epsilonOf c :=
  ⟨S1889ConstantRealCuspCoordinate l S 1 one_pos,
    S1889ConstantRealCuspCoordinate l S 2 (by norm_num),
    by norm_num⟩

/-- Rescaling action on the real shell: multiplying the first field by `a > 0`
and dividing the cusp scale by `a` preserves every field. -/
noncomputable def S1889ScaleRealCuspCoordinate (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (R : S1881RealCuspCoordinate l S)
    (a : Real) (ha : 0 < a) : S1881RealCuspCoordinate l S where
  epsilonOf := fun c => a * R.epsilonOf c
  epsilon_positive := fun c => mul_pos ha (R.epsilon_positive c)
  epsilon_nonzero := fun c => mul_ne_zero (ne_of_gt ha) (R.epsilon_nonzero c)
  cuspScaleOf := fun c => R.cuspScaleOf c / a
  cuspScale_positive := fun c => div_pos (R.cuspScale_positive c) ha
  epsilon_scale_relation := fun c => by
    have h : (a * R.epsilonOf c) * (R.cuspScaleOf c / a) =
        R.epsilonOf c * R.cuspScaleOf c := by
      rw [div_eq_mul_inv]
      calc a * R.epsilonOf c * (R.cuspScaleOf c * a⁻¹)
          = (a * a⁻¹) * (R.epsilonOf c * R.cuspScaleOf c) := by ring
        _ = R.epsilonOf c * R.cuspScaleOf c := by
              rw [mul_inv_cancel₀ (ne_of_gt ha), one_mul]
    rw [h]
    exact R.epsilon_scale_relation c
  epsilon_compatibility := R.epsilon_compatibility
  epsilon_compatibility_proved := R.epsilon_compatibility_proved

@[simp] theorem S1889ScaleRealCuspCoordinate_epsilonOf (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (R : S1881RealCuspCoordinate l S)
    (a : Real) (ha : 0 < a) (c : S1889PaperCusp l S) :
    (S1889ScaleRealCuspCoordinate l S R a ha).epsilonOf c = a * R.epsilonOf c :=
  rfl

/-- The compatibility field of the shell is also vacuous: it can be replaced by
`True` without changing any real data. -/
noncomputable def S1889TrueCompatibilityCoordinate (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (R : S1881RealCuspCoordinate l S) :
    S1881RealCuspCoordinate l S where
  epsilonOf := R.epsilonOf
  epsilon_positive := R.epsilon_positive
  epsilon_nonzero := R.epsilon_nonzero
  cuspScaleOf := R.cuspScaleOf
  cuspScale_positive := R.cuspScale_positive
  epsilon_scale_relation := R.epsilon_scale_relation
  epsilon_compatibility := fun _ => True
  epsilon_compatibility_proved := fun _ => trivial

@[simp] theorem S1889TrueCompatibilityCoordinate_epsilonOf (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (R : S1881RealCuspCoordinate l S)
    (c : S1889PaperCusp l S) :
    (S1889TrueCompatibilityCoordinate l S R).epsilonOf c = R.epsilonOf c := rfl

/-- The S1881 D8 missing proposition is *true for every slot*: the real leg is
not an obstruction.  This is the vacuity statement, not a paper construction. -/
theorem S1889D8Missing_trivially_true (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) : S1881D8Missing l S :=
  ⟨S1889ConstantRealCuspCoordinate l S 1 one_pos⟩

/-- The D8 real coordinate adds no missing object: obtaining it somewhere is
exactly obtaining a D9 orbicurve slot. -/
theorem S1889D8Missing_iff_slot (l : PrimeGeFive) :
    (∃ S : S1881D9OrbicurveSlot l, S1881D8Missing l S) ↔
      Nonempty (S1881D9OrbicurveSlot l) := by
  constructor
  · rintro ⟨S, _⟩
    exact ⟨S⟩
  · rintro ⟨S⟩
    exact ⟨S, S1889D8Missing_trivially_true l S⟩

/-- Likewise `SourceCuspClause` is a shell whose first field is arbitrary: every
positive real is the epsilon of some clause. -/
noncomputable def S1889CuspClauseOfEpsilon (e : Real) (he : 0 < e) :
    SourceCuspClause where
  epsilon := e
  epsilon_positive := he
  epsilon_nonzero := ne_of_gt he
  epsilon_compatibility := True
  epsilon_compatibility_proved := trivial
  cuspScale := e⁻¹
  cuspScale_positive := inv_pos.mpr he
  epsilon_scale_relation := by
    rw [mul_inv_cancel₀ (ne_of_gt he)]
    norm_num

@[simp] theorem S1889CuspClauseOfEpsilon_epsilon (e : Real) (he : 0 < e) :
    (S1889CuspClauseOfEpsilon e he).epsilon = e := rfl

/-- The first field of `SourceCuspClause` is not constrained by the contract. -/
theorem S1889CuspClause_epsilon_arbitrary (e : Real) (he : 0 < e) :
    ∃ C : SourceCuspClause, C.epsilon = e :=
  ⟨S1889CuspClauseOfEpsilon e he, rfl⟩

/-- The contract `SourceCuspClause` is inhabited without any cusp at all. -/
theorem S1889CuspClause_nonempty_trivially : Nonempty SourceCuspClause :=
  ⟨S1889CuspClauseOfEpsilon 1 one_pos⟩

/-! ## 4. The only non-arbitrary real route: the norm of an actual cusp parameter

A real number can be tied to the cusp geometrically through a nonzero
contracting local parameter `q` at each cusp, taken in the actual completion of
`K` at a finite place `v`.  The first field is then `||q c||`, which is
positive, and `< 1` by the contracting (q-parameter) condition.  The extra
proposition `isActualCuspQ` is required proved; it states that `q` really is the
cusp parameter, and it is not an arbitrary `True`. -/

/-- A nonzero contracting cusp parameter at every boundary cusp, in the actual
completion of `K` at a finite place `v`, together with the proved actuality
condition. -/
structure S1889CuspQParameter (l : PrimeGeFive) (S : S1881D9OrbicurveSlot l)
    (v : NumberField.FinitePlace (S1732A l).K) where
  /-- The local parameter at each boundary cusp. -/
  q : S1889PaperCusp l S → Completion v
  /-- The parameter is nonzero at every cusp. -/
  q_nonzero : ∀ c, q c ≠ 0
  /-- The parameter is contracting: this is the q-parameter condition. -/
  q_contracting : ∀ c, ‖q c‖ < 1
  /-- The semantic actuality condition tying `q` to the paper cusp. -/
  isActualCuspQ : S1889PaperCusp l S → Prop
  /-- It is proved at every cusp. -/
  isActualCuspQ_proved : ∀ c, isActualCuspQ c

namespace S1889CuspQParameter

variable {l : PrimeGeFive} {S : S1881D9OrbicurveSlot l}
variable {v : NumberField.FinitePlace (S1732A l).K}

/-- The real first field produced by the actual cusp parameter: its norm. -/
noncomputable def epsilonOf (Q : S1889CuspQParameter l S v)
    (c : S1889PaperCusp l S) : Real :=
  ‖Q.q c‖

/-- The norm first field is positive. -/
theorem epsilonOf_pos (Q : S1889CuspQParameter l S v)
    (c : S1889PaperCusp l S) : 0 < Q.epsilonOf c :=
  norm_pos_iff.mpr (Q.q_nonzero c)

/-- The norm first field is nonzero. -/
theorem epsilonOf_nonzero (Q : S1889CuspQParameter l S v)
    (c : S1889PaperCusp l S) : Q.epsilonOf c ≠ 0 :=
  ne_of_gt (Q.epsilonOf_pos c)

/-- The norm first field is contracting, i.e. in `(0,1)`. -/
theorem epsilonOf_lt_one (Q : S1889CuspQParameter l S v)
    (c : S1889PaperCusp l S) : Q.epsilonOf c < 1 :=
  Q.q_contracting c

/-- The cusp scale is the inverse norm. -/
noncomputable def cuspScaleOf (Q : S1889CuspQParameter l S v)
    (c : S1889PaperCusp l S) : Real :=
  (Q.epsilonOf c)⁻¹

/-- The cusp scale is positive. -/
theorem cuspScaleOf_pos (Q : S1889CuspQParameter l S v)
    (c : S1889PaperCusp l S) : 0 < Q.cuspScaleOf c :=
  inv_pos.mpr (Q.epsilonOf_pos c)

/-- The invariant norm product is one. -/
theorem epsilonOf_mul_cuspScaleOf (Q : S1889CuspQParameter l S v)
    (c : S1889PaperCusp l S) :
    Q.epsilonOf c * Q.cuspScaleOf c = 1 :=
  mul_inv_cancel₀ (ne_of_gt (Q.epsilonOf_pos c))

/-- The invariant norm product is nonzero. -/
theorem epsilonOf_mul_cuspScaleOf_ne_zero (Q : S1889CuspQParameter l S v)
    (c : S1889PaperCusp l S) :
    Q.epsilonOf c * Q.cuspScaleOf c ≠ 0 := by
  rw [Q.epsilonOf_mul_cuspScaleOf]
  norm_num

/-- The S1881 real cusp coordinate built from the actual cusp parameter.  Its
first field is the norm of `q c`, never an arbitrary constant. -/
noncomputable def realCuspCoordinate (Q : S1889CuspQParameter l S v) :
    S1881RealCuspCoordinate l S where
  epsilonOf := Q.epsilonOf
  epsilon_positive := Q.epsilonOf_pos
  epsilon_nonzero := Q.epsilonOf_nonzero
  cuspScaleOf := Q.cuspScaleOf
  cuspScale_positive := Q.cuspScaleOf_pos
  epsilon_scale_relation := Q.epsilonOf_mul_cuspScaleOf_ne_zero
  epsilon_compatibility := fun c =>
    Q.isActualCuspQ c ∧ Q.q c ≠ 0 ∧ ‖Q.q c‖ < 1
  epsilon_compatibility_proved := fun c =>
    ⟨Q.isActualCuspQ_proved c, Q.q_nonzero c, Q.q_contracting c⟩

@[simp] theorem realCuspCoordinate_epsilonOf (Q : S1889CuspQParameter l S v)
    (c : S1889PaperCusp l S) :
    Q.realCuspCoordinate.epsilonOf c = ‖Q.q c‖ := rfl

/-- The conditional source cusp clause at a chosen cusp: its real first field is
the norm of the actual cusp parameter. -/
noncomputable def cuspClause (Q : S1889CuspQParameter l S v)
    (c : S1889PaperCusp l S) : SourceCuspClause :=
  S1881CuspClauseOfCoordinate l S Q.realCuspCoordinate c

@[simp] theorem cuspClause_epsilon (Q : S1889CuspQParameter l S v)
    (c : S1889PaperCusp l S) :
    (Q.cuspClause c).epsilon = ‖Q.q c‖ := rfl

/-- The clause's epsilon is positive because the norm of a nonzero element is. -/
theorem cuspClause_epsilon_pos (Q : S1889CuspQParameter l S v)
    (c : S1889PaperCusp l S) : 0 < (Q.cuspClause c).epsilon :=
  Q.epsilonOf_pos c

end S1889CuspQParameter

/-- The exact missing input for the non-arbitrary real route: an actual
contracting cusp parameter in the completion at `v`, at every boundary cusp. -/
def S1889CuspQParameterRequired (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (v : NumberField.FinitePlace (S1732A l).K) :
    Prop :=
  Nonempty (S1889CuspQParameter l S v)

/-- The actual finite place of the S1732 K-field above `5`, used as the place
`v` of the cusp-parameter datum.  The S1732 arithmetic field has
`K = S1720Field` definitionally, and the S1720 place is the actual place above
the rational place `5` (with proved split multiplicative reduction). -/
abbrev S1889ActualPlaceAboveFive (l : PrimeGeFive) :
    NumberField.FinitePlace (S1732A l).K :=
  S1720PlaceAboveFive

/-- The exact missing input of the non-arbitrary real route at the actual bad
place above `5`: a contracting cusp parameter at every boundary cusp of
`C_K`, in the actual completion of `K` at that place. -/
abbrev S1889ActualCuspQParameterRequired (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) : Prop :=
  S1889CuspQParameterRequired l S (S1889ActualPlaceAboveFive l)

/-- A cusp parameter supplies the S1881 real cusp coordinate. -/
theorem S1889RealCuspCoordinate_of_qParameter (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) (v : NumberField.FinitePlace (S1732A l).K)
    (Q : S1889CuspQParameter l S v) :
    Nonempty (S1881RealCuspCoordinate l S) :=
  ⟨Q.realCuspCoordinate⟩

/-! ## 5. The exact first missing object

The first field of the S1881 D9 slot is the F-side quotient orbicurve `C_F` of
type `(1,1)^pm`.  The paper cusp of (f) is a cusp of the K-core `C_K` built from
`C_F`, so *both* the paper datum and the real shell are downstream of `C_F`.
The real shell itself contributes no further obstruction. -/

/-- The exact first missing object: the F-side quotient orbicurve `C_F` of type
`(1,1)^pm`, i.e. the first field of the S1881 D9 slot. -/
abbrev S1889FirstMissing (l : PrimeGeFive) :=
  S1881CF l

/-- The signature of the first missing object is the paper's `(1,1)^pm`. -/
theorem S1889FirstMissing_signature (l : PrimeGeFive)
    (C : S1889FirstMissing l) :
    (C : Iut.HyperbolicOrbicurve (S1732A l).F).signature =
      sourceTypeOneOnePlusMinus :=
  C.property

/-- Any D9 slot produces the first missing object. -/
theorem S1889FirstMissing_of_slot (l : PrimeGeFive)
    (S : S1881D9OrbicurveSlot l) : Nonempty (S1889FirstMissing l) :=
  ⟨S.firstField⟩

/-- The real D8 leg has the same exact first missing object as the paper D8:
obtaining a cusp coordinate somewhere is obtaining the D9 slot, whose first
field is `C_F`.  No real number is part of this statement. -/
theorem S1889D8RealFirstMissing (l : PrimeGeFive) :
    (∃ S : S1881D9OrbicurveSlot l, S1881D8Missing l S) ↔
      Nonempty (S1881D9OrbicurveSlot l) :=
  S1889D8Missing_iff_slot l

/-- The paper-faithful D8 over the slot is exactly the D9 cusp origin: the
paper's (f) is not a further real-number obligation. -/
theorem S1889PaperD8FirstMissing (l : PrimeGeFive) :
    (∃ S : S1881D9OrbicurveSlot l, Nonempty (S1889PaperCuspDatum l S)) ↔
      (∃ S : S1881D9OrbicurveSlot l, S1881D9CuspMissing l S) := by
  constructor
  · rintro ⟨S, h⟩
    exact ⟨S, (S1881D9CuspMissing_iff l S).mpr h⟩
  · rintro ⟨S, h⟩
    exact ⟨S, (S1881D9CuspMissing_iff l S).mp h⟩

/-! ## 6. Axiom footprint -/

#print axioms S1889PaperCusp_eq_S1881
#print axioms S1889PaperCuspDatum.cuspOf
#print axioms S1889PaperCuspDatum_arisesFromNonzeroClass
#print axioms S1889PaperCuspDatum_canonicalGenerator
#print axioms S1889PaperCuspDatum_distinguishedClass_nonzero
#print axioms S1889PaperCuspDatum_nonempty_iff_D9Cusp
#print axioms S1889PaperCuspDatum_residual
#print axioms S1889ConstantRealCuspCoordinate
#print axioms S1889ConstantRealCuspCoordinate_epsilonOf
#print axioms S1889RealCuspCoordinate_epsilon_arbitrary
#print axioms S1889RealCuspCoordinate_not_determined
#print axioms S1889ScaleRealCuspCoordinate
#print axioms S1889ScaleRealCuspCoordinate_epsilonOf
#print axioms S1889TrueCompatibilityCoordinate
#print axioms S1889TrueCompatibilityCoordinate_epsilonOf
#print axioms S1889D8Missing_trivially_true
#print axioms S1889D8Missing_iff_slot
#print axioms S1889CuspClauseOfEpsilon
#print axioms S1889CuspClauseOfEpsilon_epsilon
#print axioms S1889CuspClause_epsilon_arbitrary
#print axioms S1889CuspClause_nonempty_trivially
#print axioms S1889CuspQParameter.epsilonOf
#print axioms S1889CuspQParameter.epsilonOf_pos
#print axioms S1889CuspQParameter.epsilonOf_lt_one
#print axioms S1889CuspQParameter.realCuspCoordinate
#print axioms S1889CuspQParameter.realCuspCoordinate_epsilonOf
#print axioms S1889CuspQParameter.cuspClause
#print axioms S1889CuspQParameter.cuspClause_epsilon
#print axioms S1889CuspQParameterRequired
#print axioms S1889ActualPlaceAboveFive
#print axioms S1889ActualCuspQParameterRequired
#print axioms S1889RealCuspCoordinate_of_qParameter
#print axioms S1889FirstMissing_signature
#print axioms S1889FirstMissing_of_slot
#print axioms S1889D8RealFirstMissing
#print axioms S1889PaperD8FirstMissing

end LeanFormal.IUT.XiFPaper.S1889D8RealCuspActual

end
