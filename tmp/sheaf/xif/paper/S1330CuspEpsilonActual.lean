import tmp.sheaf.xif.paper.S1320SectionsCuspActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion

/-!
# S1330: the source of the cusp epsilon and the exact real first field

## Paper source: epsilon is a cusp, not a real

IUT I, Definition 3.1(f) (text-extraction lines 3273-3283) says:

  (f) epsilon is a cusp of the hyperbolic orbicurve C_K [cf. (d)] that arises
  from a nonzero element of the quotient Q ... If v in V_bad, then we assume
  that epsilon_v is the cusp that arises from the canonical generator
  [up to sign] +-1 ...

The initial Theta-data tuple is (Fbar/F, X_F, l, C_K, V, V_bad_mod,
epsilon); see IUT I lines 3280-3283 and IUT IV lines 2679-2683.  Thus the
paper's epsilon is the selected cusp itself.  Definition 3.1(f) does not
attach a real number to it.

The faithful Lean record keeps this type: SourceSignQuotientData.epsilon has
type Iut.OrbicurveBoundaryCusp S.cK (SourceDefinition31Quantifiers.lean:619).
The legacy clause F record SourceCuspDatum likewise stores epsilon in its
carrier together with the nonzero-quotient, canonical-generator and
sign-ambiguity fields (SourceInitialThetaData.lean:2637-2644).

## The current contract

The current SourceCuspClause has instead

  epsilon : Real

as its first field (SourceDefinition31Boundary.lean:564-572), with positivity,
nonzeroness, an opaque compatibility proposition, a positive cuspScale, and
the relation epsilon * cuspScale != 0.  This real field is an added real
cusp-coordinate / source card.  It is not the paper's cusp, and it is not the
q-parameter: SourceReductionClause already carries qParameter : Bad -> Real
(SourceDefinition31Boundary.lean:101-105).

## Actual Gaussian data (S1320)

S1320 constructs the actual cusp point of the base-changed split curve and
proves that its projective coordinates are [0 : 1 : 0]
(S1320SectionsCuspActual.lean:517-528).  It also proves that the actual
q-parameter norm is gaussianFiveThetaQ = 1/5
(S1320SectionsCuspActual.lean:533-542).  The Example36 projective-closure model
of the point at infinity has the same coordinates [X:Y:Z] = [0:1:0] and
affine chart coordinates (s,t) = (0,0)
(Example36CurveProjectiveClosure.lean:164-167).

## Findings formalized below

1. q is not forced to be epsilon.  The first field of the current contract is
   unconstrained by the rest of the clause: for every positive real e and
   every clause C, rescaling produces a clause C' with C'.epsilon = e, the
   same compatibility proposition, and the same invariant product
   epsilon * cuspScale.  Hence choosing epsilon = q = 1/5 is a choice, not a
   consequence of the actual q.

2. log q = -log 5 < 0, so log q cannot be epsilon, whose field demands
   positivity.  The positive quantity -log q = log 5 is the q-pilot
   log-magnitude, not the paper's cusp epsilon.

3. The projective cusp point gives no canonical positive coordinate.  Every
   representative of [0:1:0] has x = 0 and z = 0, so those coordinates cannot
   be positive; and [0:1:0] = [0:2:0] is the same point with different raw
   Y-coordinates.  Normalizing Y = 1 is an extra chart choice and yields the
   constant 1, which carries no cusp information.  A real cusp epsilon
   requires an extra chart/coordinate source card, not just the point.

## Conclusion

The exact first field of the current contract is Real, and the exact
decomposition is first field plus tail.  The exact missing object is
S1330RealCuspCoordinate: a real coordinate map on the faithful paper cusp
OrbicurveBoundaryCusp S.cK.  This file constructs no inhabitant of that
structure, no arbitrary real, and no q = 1/5 substitution.

## Axiom footprint

All checks at the end are expected to depend only on propext,
Classical.choice and Quot.sound.  No sorry is used.

-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1320SectionsCuspActual
open scoped WeierstrassCurve.Projective

local instance s1330GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1330FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. Paper source of epsilon: a cusp, not a real -/

/-- The faithful paper cusp carrier over an actual Gaussian arithmetic input:
Definition 3.1(f) gives a geometric boundary cusp. -/
abbrev S1330PaperCusp (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Type 1 :=
  Iut.OrbicurveBoundaryCusp S.cK

/-- The faithful source field epsilon is a cusp of C_K, not a real. -/
def S1330PaperEpsilon (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) :
    S1330PaperCusp l S :=
  S.epsilon

/-- The exact first field of the current contract is a real number. -/
abbrev S1330CurrentFirstField : Type := Real

/-! ## 2. The actual Gaussian cusp and q -/

/-- The actual cusp point is the projective point [0 : 1 : 0]. -/
theorem S1330ActualCusp_coordinates (l : PrimeGeFive) :
    (S1320ActualCuspPoint l).point =
      (⟦![0, 1, 0]⟧ :
        WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) :=
  S1320ActualCuspPoint_point l

/-- The actual q-parameter norm is 1/5. -/
theorem S1330ActualQ_value (l : PrimeGeFive) :
    S1320ActualQ l = (5 : ℝ)⁻¹ :=
  S1320ActualQ_eq l

/-- log q = -log 5, hence negative. -/
theorem S1330ActualLogQ_neg (l : PrimeGeFive) :
    Real.log (S1320ActualQ l) < 0 := by
  rw [S1320ActualQ_eq, Real.log_inv]
  have h : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  linarith

/-- The logarithm of the actual q cannot be the cusp epsilon: epsilon is
positive. -/
theorem S1330ActualLogQ_ne_epsilon (l : PrimeGeFive) (C : SourceCuspClause) :
    C.epsilon ≠ Real.log (S1320ActualQ l) := by
  intro h
  have hpos : 0 < C.epsilon := C.epsilon_positive
  rw [h] at hpos
  have hneg := S1330ActualLogQ_neg l
  linarith

/-- -log q = log 5 is positive. -/
theorem S1330ActualNegLogQ_pos (l : PrimeGeFive) :
    0 < -Real.log (S1320ActualQ l) := by
  have h := S1330ActualLogQ_neg l
  linarith

/-- -log q = log 5 exactly. -/
theorem S1330ActualNegLogQ_eq_log_five (l : PrimeGeFive) :
    -Real.log (S1320ActualQ l) = Real.log (5 : ℝ) := by
  rw [S1320ActualQ_eq, Real.log_inv]
  ring

/-! ## 3. Scaling ambiguity of the current contract -/

/-- Rescale a cusp clause by a positive a: epsilon is multiplied by a and
cuspScale is divided by a.  All contract fields are preserved. -/
noncomputable def S1330ScaleCuspClause (C : SourceCuspClause)
    (a : Real) (ha : 0 < a) : SourceCuspClause where
  epsilon := a * C.epsilon
  epsilon_positive := mul_pos ha C.epsilon_positive
  epsilon_nonzero := mul_ne_zero (ne_of_gt ha) C.epsilon_nonzero
  epsilon_compatibility := C.epsilon_compatibility
  epsilon_compatibility_proved := C.epsilon_compatibility_proved
  cuspScale := C.cuspScale / a
  cuspScale_positive := div_pos C.cuspScale_positive ha
  epsilon_scale_relation := by
    have h : (a * C.epsilon) * (C.cuspScale / a) = C.epsilon * C.cuspScale := by
      field_simp
    rw [h]
    exact C.epsilon_scale_relation

@[simp] theorem S1330ScaleCuspClause_epsilon (C : SourceCuspClause)
    (a : Real) (ha : 0 < a) :
    (S1330ScaleCuspClause C a ha).epsilon = a * C.epsilon := rfl

@[simp] theorem S1330ScaleCuspClause_cuspScale (C : SourceCuspClause)
    (a : Real) (ha : 0 < a) :
    (S1330ScaleCuspClause C a ha).cuspScale = C.cuspScale / a := rfl

/-- The product epsilon * cuspScale is the scaling invariant of the current
contract. -/
def S1330CuspInvariant (C : SourceCuspClause) : Real :=
  C.epsilon * C.cuspScale

theorem S1330CuspInvariant_scaled (C : SourceCuspClause) (a : Real) (ha : 0 < a) :
    S1330CuspInvariant (S1330ScaleCuspClause C a ha) = S1330CuspInvariant C := by
  unfold S1330CuspInvariant
  rw [S1330ScaleCuspClause_epsilon, S1330ScaleCuspClause_cuspScale]
  field_simp

/-- Set the first field of a cusp clause to an arbitrary positive real by
rescaling.  This shows that the first field is not constrained by the tail. -/
noncomputable def S1330SetCuspEpsilon (C : SourceCuspClause)
    (e : Real) (he : 0 < e) : SourceCuspClause :=
  S1330ScaleCuspClause C (e / C.epsilon) (div_pos he C.epsilon_positive)

@[simp] theorem S1330SetCuspEpsilon_epsilon (C : SourceCuspClause)
    (e : Real) (he : 0 < e) :
    (S1330SetCuspEpsilon C e he).epsilon = e := by
  rw [S1330SetCuspEpsilon, S1330ScaleCuspClause_epsilon]
  field_simp [C.epsilon_nonzero]

theorem S1330SetCuspEpsilon_compatibility (C : SourceCuspClause)
    (e : Real) (he : 0 < e) :
    (S1330SetCuspEpsilon C e he).epsilon_compatibility =
      C.epsilon_compatibility := rfl

theorem S1330SetCuspEpsilon_invariant (C : SourceCuspClause)
    (e : Real) (he : 0 < e) :
    (S1330SetCuspEpsilon C e he).epsilon *
        (S1330SetCuspEpsilon C e he).cuspScale =
      C.epsilon * C.cuspScale := by
  rw [S1330SetCuspEpsilon, S1330ScaleCuspClause_epsilon,
    S1330ScaleCuspClause_cuspScale]
  field_simp [C.epsilon_nonzero]

/-- The first field of the current contract is unconstrained: for every
positive real e there is a cusp clause with epsilon = e that preserves the
compatibility proposition and the scaling invariant of the given clause. -/
theorem S1330CuspFirstField_unconstrained (C : SourceCuspClause)
    {e : Real} (he : 0 < e) :
    ∃ C' : SourceCuspClause,
      C'.epsilon = e ∧
        C'.epsilon_compatibility = C.epsilon_compatibility ∧
          C'.epsilon * C'.cuspScale = C.epsilon * C.cuspScale :=
  ⟨S1330SetCuspEpsilon C e he,
    S1330SetCuspEpsilon_epsilon C e he,
    S1330SetCuspEpsilon_compatibility C e he,
    S1330SetCuspEpsilon_invariant C e he⟩

/-- Rescaling by 2 changes the first field while preserving the compatibility
proposition and the invariant product. -/
theorem S1330CuspEpsilon_scaling_ambiguity (C : SourceCuspClause) :
    ∃ C' : SourceCuspClause,
      C'.epsilon = 2 * C.epsilon ∧ C'.epsilon ≠ C.epsilon ∧
        C'.epsilon_compatibility = C.epsilon_compatibility ∧
          C'.epsilon * C'.cuspScale = C.epsilon * C.cuspScale := by
  refine ⟨S1330ScaleCuspClause C 2 (by norm_num), rfl, ?_,
    rfl, ?_⟩
  · intro h
    rw [S1330ScaleCuspClause_epsilon] at h
    exact C.epsilon_nonzero (by linarith)
  · rw [S1330ScaleCuspClause_epsilon, S1330ScaleCuspClause_cuspScale]
    field_simp

/-! ## 4. Projective coordinates do not give a cusp epsilon -/

/-- [0 : 1 : 0] and [0 : 2 : 0] are the same cusp point with different
Y-coordinates. -/
theorem S1330CuspClass_y_not_unique (l : PrimeGeFive) :
    ∃ P Q : Fin 3 → (S1280Arithmetic l).F,
      (⟦P⟧ : WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) = ⟦Q⟧ ∧
        P 1 ≠ Q 1 := by
  refine ⟨![0, 1, 0], ![0, 2, 0], ?_, ?_⟩
  · have h2 : (2 : (S1280Arithmetic l).F) ≠ 0 := by norm_num
    have hunit : IsUnit (2 : (S1280Arithmetic l).F) := isUnit_iff_ne_zero.mpr h2
    have hsmul : (![0, 2, 0] : Fin 3 → (S1280Arithmetic l).F) =
        (2 : (S1280Arithmetic l).F) • ![0, 1, 0] := by
      ext i
      fin_cases i <;> simp
    rw [hsmul]
    exact (WeierstrassCurve.Projective.smul_eq ![0, 1, 0] hunit).symm
  · norm_num

/-- Every representative of the actual cusp has x-coordinate zero, so the
x-coordinate cannot be a positive epsilon. -/
theorem S1330CuspRep_x_zero (l : PrimeGeFive)
    {P : Fin 3 → (S1280Arithmetic l).F}
    (h : (⟦P⟧ : WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) =
      ⟦![0, 1, 0]⟧) :
    P 0 = 0 := by
  have hP : P ≈ ![0, 1, 0] := Quotient.exact h
  rcases hP with ⟨u, hu⟩
  rw [← hu]
  simp

/-- Every representative of the actual cusp has z-coordinate zero, so the
z-coordinate cannot be a positive epsilon. -/
theorem S1330CuspRep_z_zero (l : PrimeGeFive)
    {P : Fin 3 → (S1280Arithmetic l).F}
    (h : (⟦P⟧ : WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) =
      ⟦![0, 1, 0]⟧) :
    P 2 = 0 := by
  have hP : P ≈ ![0, 1, 0] := Quotient.exact h
  rcases hP with ⟨u, hu⟩
  rw [← hu]
  simp

/-! ## 5. The exact first field and the missing real cusp coordinate -/

/-- The exact first field of the current contract. -/
abbrev S1330CuspFirstField : Type := Real

/-- The exact tail of the current contract after the real first field. -/
abbrev S1330CuspTail := S1320CuspTail

/-- The exact decomposition: a current cusp clause is a real first field plus
its tail. -/
noncomputable def S1330CuspClauseEquiv :
    SourceCuspClause ≃ Sigma (fun e : S1330CuspFirstField => S1330CuspTail e) :=
  S1320CuspClauseEquiv

@[simp] theorem S1330CuspClauseEquiv_fst (C : SourceCuspClause) :
    (S1330CuspClauseEquiv C).1 = C.epsilon := rfl

/-- Exact first-field decomposition of the current cusp contract. -/
theorem S1330CuspClause_nonempty_iff_firstField_tail :
    Nonempty SourceCuspClause ↔
      ∃ e : S1330CuspFirstField, Nonempty (S1330CuspTail e) :=
  S1320CuspClause_nonempty_iff_firstField_tail

/-- A real cusp coordinate on the faithful paper cusp: this is the exact
missing object that would turn Definition 3.1(f)'s cusp into a real epsilon. -/
structure S1330RealCuspCoordinate (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) where
  epsilonOf : S1330PaperCusp l S → Real
  epsilon_positive : ∀ c, 0 < epsilonOf c
  epsilon_nonzero : ∀ c, epsilonOf c ≠ 0
  cuspScaleOf : S1330PaperCusp l S → Real
  cuspScale_positive : ∀ c, 0 < cuspScaleOf c
  epsilon_scale_relation : ∀ c, epsilonOf c * cuspScaleOf c ≠ 0
  epsilon_compatibility : S1330PaperCusp l S → Prop
  epsilon_compatibility_proved : ∀ c, epsilon_compatibility c

/-- Conditional construction of the current cusp clause from a real cusp
coordinate on the faithful paper cusp and a chosen cusp. -/
noncomputable def S1330CuspClauseOfRealCuspCoordinate
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (R : S1330RealCuspCoordinate l S) (c : S1330PaperCusp l S) :
    SourceCuspClause where
  epsilon := R.epsilonOf c
  epsilon_positive := R.epsilon_positive c
  epsilon_nonzero := R.epsilon_nonzero c
  epsilon_compatibility := R.epsilon_compatibility c
  epsilon_compatibility_proved := R.epsilon_compatibility_proved c
  cuspScale := R.cuspScaleOf c
  cuspScale_positive := R.cuspScale_positive c
  epsilon_scale_relation := R.epsilon_scale_relation c

@[simp] theorem S1330CuspClauseOfRealCuspCoordinate_epsilon
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (R : S1330RealCuspCoordinate l S) (c : S1330PaperCusp l S) :
    (S1330CuspClauseOfRealCuspCoordinate R c).epsilon = R.epsilonOf c := rfl

/-- Exact missing object: a real coordinate on the paper cusp.  This is a
Prop, so the file does not assert an inhabitant. -/
def S1330RealCuspCoordinateMissing (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Prop :=
  Nonempty (S1330RealCuspCoordinate l S)

/-! ## 6. Axiom footprint -/

#print axioms S1330PaperEpsilon
#print axioms S1330ActualCusp_coordinates
#print axioms S1330ActualQ_value
#print axioms S1330ActualLogQ_neg
#print axioms S1330ActualLogQ_ne_epsilon
#print axioms S1330ActualNegLogQ_pos
#print axioms S1330ActualNegLogQ_eq_log_five
#print axioms S1330CuspInvariant_scaled
#print axioms S1330SetCuspEpsilon_epsilon
#print axioms S1330SetCuspEpsilon_invariant
#print axioms S1330CuspFirstField_unconstrained
#print axioms S1330CuspEpsilon_scaling_ambiguity
#print axioms S1330CuspClass_y_not_unique
#print axioms S1330CuspRep_x_zero
#print axioms S1330CuspRep_z_zero
#print axioms S1330CuspClauseEquiv
#print axioms S1330CuspClause_nonempty_iff_firstField_tail
#print axioms S1330CuspClauseOfRealCuspCoordinate

end LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual

end
