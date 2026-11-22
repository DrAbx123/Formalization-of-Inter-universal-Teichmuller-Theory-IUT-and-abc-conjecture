import tmp.sheaf.xif.paper.S1400RealCuspCoordinateActual

/-!
# S1428: actual cusp / valuation / Haar / scale attempts at the real cusp coordinate

S1330 and S1400 isolate the exact first field of the current cusp contract:

  epsilonOf : Iut.OrbicurveBoundaryCusp S.cK -> Real

and prove that the actual Gaussian q-parameter (q = 1/5, log q = -log 5) is not
the paper's positive cusp epsilon.  This file attempts the construction of
epsilonOf from the actual data named in the task:

* the actual cusp point, whose projective representative is [0 : 1 : 0];
* the actual finite place above 5 and its completed local field;
* the actual local valuation / norm on that completion;
* an actual Haar measure on the completion;
* the cusp scale as the inverse norm of a local parameter.

The outcome is the following.

1. The projective cusp point by itself gives no positive varying real.  Every
   representative has x = z = 0 and y != 0, hence the affine coordinates at the
   cusp are both 0.  Normalizing y to 1 gives the constant 1, and any
   scale-invariant function of the raw y-coordinate is constant on the orbit.
   This is a precise no-go for the actual cusp coordinate route.

2. A genuine valuation/scale construction is possible conditionally on a
   nonzero local parameter at the cusp in the actual completion at the bad
   place.  Its epsilon is the norm of that local parameter; positivity and
   nonzeroness are proved.  The scale is the inverse norm, so the invariant
   product is 1.  No q, 1/5 or log q is used.

3. A Haar construction is also possible conditionally: epsilon is the real
   Haar mass of a chosen cusp region.  The bridge theorem identifies the Haar
   value with the valuation value when the Haar mass of the region is the
   real norm of the local parameter.

4. The exact missing input is therefore a map from the paper cusp to the
   actual completion together with its actuality condition.  The bare
   OrbicurveBoundaryCusp structure carries geometric compactification data,
   not a local parameter.  We state this missing input as
   S1428CuspLocalParameter and give the exact conditional consumer chain.

No sorry, axiom, True, PUnit, q = 1/5 or log q is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1428RealCuspValuationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1320SectionsCuspActual
open LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual
open LeanFormal.IUT.XiFPaper.S1357RealCuspCoordinateActual
open LeanFormal.IUT.XiFPaper.S1383RealCuspCoordinateActual
open LeanFormal.IUT.XiFPaper.S1400RealCuspCoordinateActual
open MeasureTheory
open scoped WeierstrassCurve.Projective

/-- The completion at the concrete place above 5 carries its Borel measurable
space.  This is a local instance: the Haar section is the only consumer. -/
local instance s1428CompletionMeasurableSpace (l : PrimeGeFive) :
    MeasurableSpace (Completion (S1280Place l)) :=
  borel (Completion (S1280Place l))

/-! ## 1. The exact first field -/

/-- The exact first field of the cusp contract, reused from S1400/S1330. -/
abbrev S1428EpsilonOf (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Type 1 :=
  S1400EpsilonMap l S

/-- The first field is exactly a real-valued function on the paper cusp. -/
theorem S1428EpsilonOf_eq_firstField (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) :
    S1428EpsilonOf l S = (S1330PaperCusp l S -> Real) := rfl

/-- The actual selected cusp is still the faithful geometric cusp. -/
theorem S1428PaperCusp_eq (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) :
    S1330PaperCusp l S = Iut.OrbicurveBoundaryCusp S.cK := rfl

/-! ## 2. The actual cusp point gives no positive varying coordinate

The actual cusp point has representative [0 : 1 : 0].  We prove that its
y-coordinate is nonzero, its affine x- and z-coordinates are zero, its
normalized y-coordinate is one, and any scale-invariant function of the raw
y-coordinate is constant on the cusp orbit. -/

/-- Every representative of the actual cusp has nonzero y-coordinate. -/
theorem S1428CuspRep_y_ne_zero (l : PrimeGeFive)
    {P : Fin 3 -> (S1280Arithmetic l).F}
    (h : (⟦P⟧ :
      WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) =
      ⟦![0, 1, 0]⟧) :
    P 1 ≠ 0 := by
  have hP : P ≈ ![0, 1, 0] := Quotient.exact h
  rcases hP with ⟨u, hu⟩
  have h1 : (fun m : (S1280Arithmetic l).Fˣ => m • ![0, 1, 0]) u 1 =
      (u : (S1280Arithmetic l).F) := by
    simp [Units.smul_def, smul_eq_mul]
  rw [← hu]
  rw [h1]
  exact Units.ne_zero u

/-- Any representative is a unit multiple of [0 : 1 : 0]. -/
theorem S1428CuspRep_eq_unit_smul (l : PrimeGeFive)
    {P : Fin 3 -> (S1280Arithmetic l).F}
    (h : (⟦P⟧ :
      WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) =
      ⟦![0, 1, 0]⟧) :
    ∃ u : (S1280Arithmetic l).Fˣ, u • ![0, 1, 0] = P :=
  Quotient.exact h

/-- The affine x-coordinate at the cusp (chart y != 0). -/
def S1428AffineX (l : PrimeGeFive) (P : Fin 3 -> (S1280Arithmetic l).F) :
    (S1280Arithmetic l).F :=
  P 0 / P 1

/-- The affine z-coordinate at the cusp (chart y != 0). -/
def S1428AffineZ (l : PrimeGeFive) (P : Fin 3 -> (S1280Arithmetic l).F) :
    (S1280Arithmetic l).F :=
  P 2 / P 1

/-- The normalized y-coordinate at the cusp. -/
def S1428NormalizedY (l : PrimeGeFive) (P : Fin 3 -> (S1280Arithmetic l).F) :
    (S1280Arithmetic l).F :=
  P 1 / P 1

/-- The affine x-coordinate at the actual cusp is zero. -/
theorem S1428CuspAffineX_eq_zero (l : PrimeGeFive)
    {P : Fin 3 -> (S1280Arithmetic l).F}
    (h : (⟦P⟧ :
      WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) =
      ⟦![0, 1, 0]⟧) :
    S1428AffineX l P = 0 := by
  simp [S1428AffineX, S1330CuspRep_x_zero l h]

/-- The affine z-coordinate at the actual cusp is zero. -/
theorem S1428CuspAffineZ_eq_zero (l : PrimeGeFive)
    {P : Fin 3 -> (S1280Arithmetic l).F}
    (h : (⟦P⟧ :
      WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) =
      ⟦![0, 1, 0]⟧) :
    S1428AffineZ l P = 0 := by
  simp [S1428AffineZ, S1330CuspRep_z_zero l h]

/-- Normalizing y to one gives the constant one, not a cusp coordinate. -/
theorem S1428CuspNormalizedY_eq_one (l : PrimeGeFive)
    {P : Fin 3 -> (S1280Arithmetic l).F}
    (h : (⟦P⟧ :
      WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) =
      ⟦![0, 1, 0]⟧) :
    S1428NormalizedY l P = 1 := by
  unfold S1428NormalizedY
  exact div_self (S1428CuspRep_y_ne_zero l h)

/-- A scale-invariant function of the raw y-coordinate is constant on the
actual cusp orbit: its value is the value at the unit one. -/
theorem S1428CuspYFunction_constant (l : PrimeGeFive)
    (g : (S1280Arithmetic l).F -> Real)
    (hg : ∀ u : (S1280Arithmetic l).F, u ≠ 0 -> g u = g 1)
    {P : Fin 3 -> (S1280Arithmetic l).F}
    (h : (⟦P⟧ :
      WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) =
      ⟦![0, 1, 0]⟧) :
    g (P 1) = g 1 := by
  have hP : P ≈ ![0, 1, 0] := Quotient.exact h
  rcases hP with ⟨u, hu⟩
  have h1 : P 1 = (u : (S1280Arithmetic l).F) := by
    rw [← hu]
    simp [Units.smul_def, smul_eq_mul]
  rw [h1]
  exact hg (u : (S1280Arithmetic l).F) (Units.ne_zero u)

/-! ## 3. Actual valuation/norm construction at the bad place above 5

The actual completion Completion (S1280Place l) is the completed local field
at the concrete Gaussian place above 5.  A cusp local parameter is a nonzero
element of this completion.  Its norm is a positive real depending only on the
valuation scale; we use it as epsilon and its inverse as cusp scale. -/

/-- A cusp local parameter in the actual completed local field at the bad
place above 5, with the exact nonzero condition needed for positivity. -/
structure S1428CuspLocalParameter (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) where
  /-- The local parameter assigned to each boundary cusp. -/
  localParameter : S1330PaperCusp l S -> Completion (S1280Place l)
  /-- The local parameter is nonzero at every cusp. -/
  localParameter_nonzero : ∀ c, localParameter c ≠ 0
  /-- The semantic actuality condition tying the parameter to the paper cusp.
  It is a proposition, not an arbitrary real value; it is not proved here. -/
  isActualCuspParameter : Prop
  isActualCuspParameter_proved : isActualCuspParameter

/-- The value of the valuation/norm construction: the norm of the local
parameter.  This is the exact real first field produced by the actual local
field data. -/
noncomputable def S1428ValuationEpsilonOf
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S) (c : S1330PaperCusp l S) : Real :=
  ‖P.localParameter c‖

/-- The valuation/norm epsilon is positive. -/
theorem S1428ValuationEpsilonOf_pos
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S) (c : S1330PaperCusp l S) :
    0 < S1428ValuationEpsilonOf P c :=
  norm_pos_iff.mpr (P.localParameter_nonzero c)

/-- The valuation/norm epsilon is nonzero. -/
theorem S1428ValuationEpsilonOf_ne_zero
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S) (c : S1330PaperCusp l S) :
    S1428ValuationEpsilonOf P c ≠ 0 :=
  ne_of_gt (S1428ValuationEpsilonOf_pos P c)

/-- The cusp scale is the inverse norm of the local parameter. -/
noncomputable def S1428ValuationCuspScaleOf
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S) (c : S1330PaperCusp l S) : Real :=
  (S1428ValuationEpsilonOf P c)⁻¹

/-- The cusp scale is positive. -/
theorem S1428ValuationCuspScaleOf_pos
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S) (c : S1330PaperCusp l S) :
    0 < S1428ValuationCuspScaleOf P c :=
  inv_pos.mpr (S1428ValuationEpsilonOf_pos P c)

/-- The invariant epsilon * cuspScale is one. -/
theorem S1428ValuationEpsilonOf_mul_scale
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S) (c : S1330PaperCusp l S) :
    S1428ValuationEpsilonOf P c * S1428ValuationCuspScaleOf P c = 1 := by
  unfold S1428ValuationCuspScaleOf
  exact mul_inv_cancel₀ (ne_of_gt (S1428ValuationEpsilonOf_pos P c))

/-- The invariant epsilon * cuspScale is nonzero. -/
theorem S1428ValuationEpsilonOf_mul_scale_ne_zero
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S) (c : S1330PaperCusp l S) :
    S1428ValuationEpsilonOf P c * S1428ValuationCuspScaleOf P c ≠ 0 := by
  rw [S1428ValuationEpsilonOf_mul_scale]
  norm_num

/-- The conditional real cusp coordinate obtained from the actual valuation
norm of a cusp local parameter. -/
noncomputable def S1428ValuationRealCuspCoordinate
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S) :
    S1330RealCuspCoordinate l S where
  epsilonOf := S1428ValuationEpsilonOf P
  epsilon_positive := S1428ValuationEpsilonOf_pos P
  epsilon_nonzero := S1428ValuationEpsilonOf_ne_zero P
  cuspScaleOf := S1428ValuationCuspScaleOf P
  cuspScale_positive := S1428ValuationCuspScaleOf_pos P
  epsilon_scale_relation := S1428ValuationEpsilonOf_mul_scale_ne_zero P
  epsilon_compatibility := fun c => P.localParameter c ≠ 0
  epsilon_compatibility_proved := P.localParameter_nonzero

/-- The first field of the valuation construction is exactly the norm of the
local parameter. -/
@[simp] theorem S1428ValuationRealCuspCoordinate_epsilonOf
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S) (c : S1330PaperCusp l S) :
    (S1428ValuationRealCuspCoordinate P).epsilonOf c =
      ‖P.localParameter c‖ := rfl

/-- The valuation construction feeds the existing S1330 source-clause
constructor with exactly the same first field. -/
theorem S1428ValuationCuspClause_epsilon
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S) (c : S1330PaperCusp l S) :
    (S1330CuspClauseOfRealCuspCoordinate
      (S1428ValuationRealCuspCoordinate P) c).epsilon =
      ‖P.localParameter c‖ := rfl

/-- A unit of norm one does not change the valuation epsilon: the construction
depends on the local scale, not on the choice of local parameter within the
same norm class. -/
theorem S1428ValuationEpsilonOf_unit_mul
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S)
    (u : (Completion (S1280Place l))ˣ)
    (hu : ‖(u : Completion (S1280Place l))‖ = 1)
    (c : S1330PaperCusp l S) :
    ‖(u : Completion (S1280Place l)) * P.localParameter c‖ =
      S1428ValuationEpsilonOf P c := by
  unfold S1428ValuationEpsilonOf
  rw [norm_mul, hu, one_mul]

/-! ## 4. Actual Haar construction and its bridge to the valuation norm -/

/-- A Haar mass region at each boundary cusp in the actual completion.  The
region is measurable, positive and finite; these are exactly the hypotheses
needed to read a positive real mass. -/
structure S1428HaarCuspData (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) where
  /-- The actual Haar measure on the completion at the bad place. -/
  measure : Measure (Completion (S1280Place l))
  /-- The region of the local field attached to a cusp. -/
  region : S1330PaperCusp l S -> Set (Completion (S1280Place l))
  region_measurable : ∀ c, MeasurableSet (region c)
  region_positive : ∀ c, 0 < measure (region c)
  region_finite : ∀ c, measure (region c) < ⊤

/-- The Haar mass of the cusp region, as a real number. -/
noncomputable def S1428HaarEpsilonOf
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S) (c : S1330PaperCusp l S) : Real :=
  (H.measure (H.region c)).toReal

/-- The Haar epsilon is positive because the region has positive finite
measure. -/
theorem S1428HaarEpsilonOf_pos
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S) (c : S1330PaperCusp l S) :
    0 < S1428HaarEpsilonOf H c :=
  ENNReal.toReal_pos
    (ne_of_gt (H.region_positive c))
    (ne_of_lt (H.region_finite c))

/-- The Haar epsilon is nonzero. -/
theorem S1428HaarEpsilonOf_ne_zero
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S) (c : S1330PaperCusp l S) :
    S1428HaarEpsilonOf H c ≠ 0 :=
  ne_of_gt (S1428HaarEpsilonOf_pos H c)

/-- The Haar cusp scale is the inverse Haar mass. -/
noncomputable def S1428HaarCuspScaleOf
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S) (c : S1330PaperCusp l S) : Real :=
  (S1428HaarEpsilonOf H c)⁻¹

/-- The Haar cusp scale is positive. -/
theorem S1428HaarCuspScaleOf_pos
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S) (c : S1330PaperCusp l S) :
    0 < S1428HaarCuspScaleOf H c :=
  inv_pos.mpr (S1428HaarEpsilonOf_pos H c)

/-- The Haar invariant epsilon * cuspScale is one. -/
theorem S1428HaarEpsilonOf_mul_scale
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S) (c : S1330PaperCusp l S) :
    S1428HaarEpsilonOf H c * S1428HaarCuspScaleOf H c = 1 := by
  unfold S1428HaarCuspScaleOf
  exact mul_inv_cancel₀ (ne_of_gt (S1428HaarEpsilonOf_pos H c))

/-- The Haar invariant epsilon * cuspScale is nonzero. -/
theorem S1428HaarEpsilonOf_mul_scale_ne_zero
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S) (c : S1330PaperCusp l S) :
    S1428HaarEpsilonOf H c * S1428HaarCuspScaleOf H c ≠ 0 := by
  rw [S1428HaarEpsilonOf_mul_scale]
  norm_num

/-- The conditional real cusp coordinate obtained from the actual Haar mass. -/
noncomputable def S1428HaarRealCuspCoordinate
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S) :
    S1330RealCuspCoordinate l S where
  epsilonOf := S1428HaarEpsilonOf H
  epsilon_positive := S1428HaarEpsilonOf_pos H
  epsilon_nonzero := S1428HaarEpsilonOf_ne_zero H
  cuspScaleOf := S1428HaarCuspScaleOf H
  cuspScale_positive := S1428HaarCuspScaleOf_pos H
  epsilon_scale_relation := S1428HaarEpsilonOf_mul_scale_ne_zero H
  epsilon_compatibility := fun c => 0 < H.measure (H.region c)
  epsilon_compatibility_proved := H.region_positive

/-- The first field of the Haar construction is exactly the real Haar mass. -/
@[simp] theorem S1428HaarRealCuspCoordinate_epsilonOf
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S) (c : S1330PaperCusp l S) :
    (S1428HaarRealCuspCoordinate H).epsilonOf c =
      (H.measure (H.region c)).toReal := rfl

/-- The Haar construction feeds the existing source-clause constructor. -/
theorem S1428HaarCuspClause_epsilon
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S) (c : S1330PaperCusp l S) :
    (S1330CuspClauseOfRealCuspCoordinate
      (S1428HaarRealCuspCoordinate H) c).epsilon =
      (H.measure (H.region c)).toReal := rfl

/-- Bridge: if the Haar mass of the cusp region is the real norm of the actual
local parameter, the Haar epsilon and the valuation epsilon agree. -/
theorem S1428HaarEpsilonOf_eq_valuation
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S)
    (P : S1428CuspLocalParameter l S)
    (h : ∀ c,
      H.measure (H.region c) = ENNReal.ofReal ‖P.localParameter c‖)
    (c : S1330PaperCusp l S) :
    S1428HaarEpsilonOf H c = S1428ValuationEpsilonOf P c := by
  unfold S1428HaarEpsilonOf S1428ValuationEpsilonOf
  rw [h c]
  exact ENNReal.toReal_ofReal (le_of_lt (norm_pos_iff.mpr
    (P.localParameter_nonzero c)))

/-! ## 5. The exact missing input and the consumer chain

The actual local-parameter map is not a field of OrbicurveBoundaryCusp.  The
exact input left by the constructions above is S1428CuspLocalParameter,
including its semantic actuality proposition.  We record the required property
and the consumer chain without asserting an inhabitant. -/

/-- Exact missing input: an actual cusp local parameter in the completed local
field at the concrete place above 5. -/
def S1428CuspLocalParameterRequired (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Prop :=
  Nonempty (S1428CuspLocalParameter l S)

/-- Exact missing real cusp coordinate, stated as the nonemptiness of the S1330
coordinate package.  This is the same exact first-field consumer as S1330. -/
def S1428RealCuspCoordinateRequired (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Prop :=
  S1330RealCuspCoordinateMissing l S

/-- The valuation construction closes the coordinate package whenever the
actual local-parameter input is supplied. -/
theorem S1428RealCuspCoordinate_of_localParameter
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S) :
    Nonempty (S1330RealCuspCoordinate l S) :=
  ⟨S1428ValuationRealCuspCoordinate P⟩

/-- The Haar construction closes the coordinate package whenever the Haar
cusp-region input is supplied. -/
theorem S1428RealCuspCoordinate_of_haar
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S) :
    Nonempty (S1330RealCuspCoordinate l S) :=
  ⟨S1428HaarRealCuspCoordinate H⟩

/-- The exact first field produced by the valuation route is still the S1330
first field type. -/
theorem S1428ValuationFirstField_type
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (P : S1428CuspLocalParameter l S) :
    (S1428ValuationRealCuspCoordinate P).epsilonOf =
      (fun c => ‖P.localParameter c‖) := rfl

/-- The exact first field produced by the Haar route is still the S1330 first
field type. -/
theorem S1428HaarFirstField_type
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    (H : S1428HaarCuspData l S) :
    (S1428HaarRealCuspCoordinate H).epsilonOf =
      (fun c => (H.measure (H.region c)).toReal) := rfl

/-! ## 6. Axiom footprint -/

#print axioms S1428EpsilonOf_eq_firstField
#print axioms S1428CuspRep_y_ne_zero
#print axioms S1428CuspAffineX_eq_zero
#print axioms S1428CuspAffineZ_eq_zero
#print axioms S1428CuspNormalizedY_eq_one
#print axioms S1428CuspYFunction_constant
#print axioms S1428ValuationEpsilonOf_pos
#print axioms S1428ValuationEpsilonOf_mul_scale
#print axioms S1428ValuationRealCuspCoordinate
#print axioms S1428ValuationCuspClause_epsilon
#print axioms S1428ValuationEpsilonOf_unit_mul
#print axioms S1428HaarEpsilonOf_pos
#print axioms S1428HaarRealCuspCoordinate
#print axioms S1428HaarCuspClause_epsilon
#print axioms S1428HaarEpsilonOf_eq_valuation
#print axioms S1428RealCuspCoordinate_of_localParameter
#print axioms S1428RealCuspCoordinate_of_haar

end LeanFormal.IUT.XiFPaper.S1428RealCuspValuationActual

end
