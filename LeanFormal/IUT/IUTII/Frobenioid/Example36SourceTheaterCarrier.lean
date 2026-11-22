import LeanFormal.IUT.IUTII.Frobenioid.ConcreteSourceFrobenioidBridge
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelDivisor
import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamily
import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkDivisorMonoidDisplacementReduction
import LeanFormal.IUT.Audit.Status

/-!
  # The concrete source Hodge-theater carrier of the Gaussian C-stage and its
  identification with the concrete Frobenioid backend

  Task task-20 of the Group-1 ("actual Hodge-theater/link carrier identification
  with the concrete Frobenioid backend") split.  The frozen contract asks for a
  concrete source Hodge-theater carrier built from *actual* initial Theta-data
  (not an identity-link or constant-q finite model), a proof that its local
  Frobenioid data agrees with the concrete stage model of
  ConcreteSourceFrobenioidBridge.lean, an identification of the linked local
  carrier with the Example 3.6 backend/place data where this is definitionally
  possible, and otherwise the *exact* obstruction.

  ## What is constructed and proved here

  * sourceTheater is the concrete Hodge theater carried by the actual C-stage
    concreteInitialThetaCStage l: arithmetic input
    concreteGaussianInitialThetaArithmeticData l (the actual quadratic field
    Q(i), the base-changed split multiplicative curve, and the actual finite
    place concreteGaussianFivePlace above 5), the actual nonzero
    integral-closure prime strip finiteLocalIntegralFPrimeStrip 2 7, and the
    actual finite theta packet FiniteThetaPacket.ofQ gaussianFiveThetaQ ...
    whose q is the norm of the actual local q-parameter
    localQParameterFor 5.  The q-value is computed exactly: it is 1/5, so the
    carrier is *not* a constant/normalized-q model.
  * concreteSourceFrobenioidBoundary l is proved to be the boundary of the
    same C-stage: the theater of the boundary is sourceTheater, its actual
    place is concreteGaussianFivePlace, its model is concreteStageModel, its
    model input is concreteStageModelInput, and its local Kummer finite kernel
    is zmultiples l.  The stage model's divisorial monoid object is identified
    with the concrete finite-stage divisorial monoid.
  * At the concrete place the Example 3.6 number-field place data
    (numberFieldGlobalPlaceData), the Example 3.6 model-Frobenioid divisor
    input (globalModelDivisor), and the principal-divisor realized backend
    object are identified with the actual v-adic valuation exponent on global
    units.  The concrete place is proved to lie above the rational prime 5,
    the same rational prime as the finite prime strip's selected local label.
    The local norm-log degree of the finite-strip q-parameter is therefore
    -log 5, i.e. minus the log of the rational prime below the stage-model
    place.
  * Exact obstructions are proved: every HodgeTheaterLink out of the concrete
    carrier transports its q-value, so no link can reach a constant-q model
    (q = 1/2, q = 1, or any other value); a SourceHodgeTheaterFamily whose
    theaters are all the single concrete carrier has a subsingleton index (so
    the reflexive concrete history cannot stand in for the paper's distinct
    histories); and the reflexive history carried by the C-stage is recorded to
    be exactly an identity-prime-strip, equality-of-q test history.

  ## What is NOT proved (honest boundary; nothing below is assumed as a field)

  * The paper's Hodge theater over the *actual place set* of the Gaussian field
    is not constructed.  The tree's concrete prime strip is the finite-interval
    carrier FinitePrimePlace 2 7 (the audited finite model of the bad-prime
    set), not the place-indexed prime strip of IUT I, Definition 5.2; no
    identification of the two index types is asserted.
  * The source theta generators, the anabelian theta and log links between
    distinct theaters, and the distinct histories of OriginalInput.family are
    not constructed.  The only history available at the concrete carrier is
    the reflexive ConcreteInitialThetaHistory, whose links are identity
    prime-strip equalities; Section 4 proves that such a history cannot serve
    as a family of distinct histories.
  * The identification of the stage-model normalized valuation
    stageNormalizedAdditiveValuation at the terminal stage with the Example
    3.6 valuation finitePlaceValueExponent on global units (through the
    completion Valued.v and the normalization iso of
    SourceFiniteStageDivisorTransition) is not proved here.  Both sides are
    realized at the same concrete place, and the place data of the backend is
    identified with the actual valuation exponent, but the stage-model
    normalization bridge remains a named residual input; it is never assumed.
  * No theta-pilot, q-pilot, Tate-uniformization, Hodge-Arakelov, or source
    identification beyond the stated equalities is claimed.

  Source correspondence: IUT I, Definition 3.1 and Sections 4-5 (initial Theta
  data, Hodge theaters, histories and links); IUT II, Definition 4.9(i) (local
  integral F-prime strip); IUT III, Example 3.6 (finite-stage model
  Frobenioid and place data); the corpus references are the ones already fixed
  in ConcreteSourceFrobenioidBridge.lean, Example36NumberFieldPlaceData.lean
  and ConcreteInitialThetaCStage.lean.
-/


set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace SourceTheaterCarrier

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.IUTII.Frobenioid.Example36

/- The Gaussian field instances needed to state the place-level identifications:
GaussianField is an AdjoinRoot, whose field structure needs the checked
irreducibility fact, and the concrete carriers are instances of the actual
prime 5 and of the ambient prime l. -/
local instance gaussianPolynomialIrreducibleFactSourceTheater :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactSourceTheater : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactSourceTheater (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

noncomputable section

universe ua upi umon ui

/-! ## 1. The concrete source theater carrier -/

/-- The concrete Hodge-theater carrier built from the actual initial Theta-data
of the Gaussian C-stage: the theater field of concreteInitialThetaCStage l.
Its arithmetic input is the actual Q(i) initial Theta data with the
base-changed split multiplicative curve, its prime strip is the actual nonzero
integral-closure F-prime strip on the finite interval [2, 7], and its theta
packet is the actual finite packet with q the norm of the local q-parameter. -/
def sourceTheater (l : PrimeGeFive) : HodgeTheater l (FinitePrimePlace 2 7) :=
  (concreteInitialThetaCStage l).theater

@[simp] theorem sourceTheater_eq_cStage_theater (l : PrimeGeFive) :
    sourceTheater l = (concreteInitialThetaCStage l).theater :=
  rfl

/-- The arithmetic input of the concrete carrier is the actual Gaussian initial
Theta data (not a free parameter and not an identity-level model). -/
theorem sourceTheater_arithmetic (l : PrimeGeFive) :
    (sourceTheater l).arithmetic = concreteGaussianInitialThetaArithmeticData l :=
  ((concreteInitialThetaCStage l).theater_arithmetic).trans
    (concreteInitialThetaPlaceInput_arithmetic l)

/-- The number field of the concrete carrier is the actual number field Q(i) of
the checked arithmetic example. -/
theorem sourceTheater_arithmetic_F (l : PrimeGeFive) :
    (sourceTheater l).arithmetic.F = GaussianField := by
  unfold sourceTheater
  rfl

/-- The curve of the concrete carrier is the actual base-changed split
multiplicative curve of the checked finite-place boundary. -/
theorem sourceTheater_arithmetic_curve (l : PrimeGeFive) :
    (sourceTheater l).arithmetic.curve =
      concreteSplitPuncturedCurve.baseChange GaussianField := by
  unfold sourceTheater
  exact concreteGaussianInitialThetaArithmeticData_curve l

/-- The prime strip of the concrete carrier is the actual nonzero
integral-closure F-prime strip on the finite interval [2, 7]; it is not the
identity carrier. -/
@[simp] theorem sourceTheater_primeStrip (l : PrimeGeFive) :
    (sourceTheater l).primeStrip = finiteLocalIntegralFPrimeStrip 2 7 :=
  rfl

/-- The theta packet of the concrete carrier is the actual finite Gaussian
packet with q the norm gaussianFiveThetaQ of the local q-parameter. -/
@[simp] theorem sourceTheater_thetaPacket (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket =
      FiniteThetaPacket.ofQ gaussianFiveThetaQ gaussianFiveThetaQ_pos :=
  rfl

/-- The q-value of the concrete carrier is the actual norm of the local
q-parameter at 5. -/
theorem sourceTheater_theta_q (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.q = gaussianFiveThetaQ := by
  rw [sourceTheater_thetaPacket]
  rfl

/-- The actual local q-parameter norm gaussianFiveThetaQ is 1/5. -/
theorem gaussianFiveThetaQ_eq_inv_five :
    gaussianFiveThetaQ = (5 : ℝ)⁻¹ := by
  unfold gaussianFiveThetaQ
  exact localQParameterFor_norm_eq_inv 5

/-- The q-value of the concrete carrier is exactly 1/5. -/
theorem sourceTheater_theta_q_eq_inv_five (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.q = (5 : ℝ)⁻¹ := by
  rw [sourceTheater_theta_q, gaussianFiveThetaQ_eq_inv_five]

theorem sourceTheater_theta_q_pos (l : PrimeGeFive) :
    0 < (sourceTheater l).thetaPacket.q := by
  rw [sourceTheater_theta_q]
  exact gaussianFiveThetaQ_pos

theorem sourceTheater_theta_q_ne_zero (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.q ≠ 0 :=
  ne_of_gt (sourceTheater_theta_q_pos l)

/-- The q-value is strictly below one: the actual local q-parameter is
contracting, so the carrier is not the normalized/constant-q = 1 model. -/
theorem sourceTheater_theta_q_lt_one (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.q < 1 := by
  rw [sourceTheater_theta_q_eq_inv_five]
  norm_num

theorem sourceTheater_theta_q_ne_one (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.q ≠ 1 :=
  ne_of_lt (sourceTheater_theta_q_lt_one l)

/-- The q-value is not the value 1/2 of the degenerate constant-q finite model
(SourceProcessionFromContract); this is the numerical content of the
constant-q model excluded clause of the frozen contract. -/
theorem sourceTheater_theta_q_ne_half (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.q ≠ (1 / 2 : ℝ) := by
  rw [sourceTheater_theta_q_eq_inv_five]
  norm_num

/-- The logarithm of the q-value is -log 5; in particular the theta packet has
nonzero q-log, unlike a normalized q = 1 model. -/
theorem gaussianFiveThetaQ_log :
    Real.log gaussianFiveThetaQ = - Real.log 5 := by
  rw [gaussianFiveThetaQ_eq_inv_five, Real.log_inv]

theorem sourceTheater_theta_q_log (l : PrimeGeFive) :
    Real.log ((sourceTheater l).thetaPacket.q) = - Real.log 5 := by
  rw [sourceTheater_theta_q, gaussianFiveThetaQ_log]

theorem sourceTheater_theta_q_log_ne_zero (l : PrimeGeFive) :
    Real.log ((sourceTheater l).thetaPacket.q) ≠ 0 := by
  rw [sourceTheater_theta_q_log]
  exact neg_ne_zero.mpr
    (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))

/-- The scales of the concrete theta packet are the actual Gaussian special
values q ^ (j ^ 2) of the actual q-value. -/
theorem sourceTheater_theta_scale (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    (sourceTheater l).thetaPacket.scale j =
      realThetaValue gaussianFiveThetaQ j.1 := by
  unfold sourceTheater
  exact concreteInitialThetaCStage_theta_scale l j

theorem sourceTheater_theta_scale_pos (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    0 < (sourceTheater l).thetaPacket.scale j := by
  rw [sourceTheater_theta_scale]
  exact realThetaValue_pos gaussianFiveThetaQ_pos j.1

/-- The log-scale of every theta value is (j ^ 2) * (-log 5); the packet is
therefore genuinely nonconstant whenever a nonzero label exists. -/
theorem sourceTheater_theta_log_scale (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    Real.log ((sourceTheater l).thetaPacket.scale j) =
      (gaussExponent j.1).toNat * (- Real.log 5) := by
  rw [sourceTheater_theta_scale, log_realThetaValue, gaussianFiveThetaQ_log]

/-- The theta log-volume of the concrete carrier, in the actual local-degree
form fixed by ConcreteInitialThetaCStage. -/
theorem sourceTheater_theta_log_volume (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat *
          Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  unfold sourceTheater
  exact concreteInitialThetaCStage_theta_log_volume l

/-! ## 2. The concrete Frobenioid backend carried by the same C-stage -/

/-- **Backend identification.**  The concrete Frobenioid boundary of
ConcreteSourceFrobenioidBridge is the boundary of exactly the C-stage that
carries the source theater: its theater is sourceTheater, its actual place is
the concrete Gaussian place, its Frobenioid presentation is the concrete stage
model, its model input is the concrete stage model input, and its local Kummer
finite kernel is zmultiples l. -/
theorem sourceTheater_stageModel_provenance (l : PrimeGeFive) :
    (concreteSourceFrobenioidBoundary l).cStage.theater = sourceTheater l ∧
    (concreteSourceFrobenioidBoundary l).cStage.place = concreteGaussianFivePlace ∧
    (concreteSourceFrobenioidBoundary l).place = concretePlace ∧
    (concreteSourceFrobenioidBoundary l).model = concreteStageModel ∧
    (concreteSourceFrobenioidBoundary l).model_input = concreteStageModelInput ∧
    (concreteSourceFrobenioidBoundary l).cStage.localCarrier.kummer.finiteReduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact concreteInitialThetaCStage_local_finite_kernel l

/-- The local divisorial monoid of the concrete stage model at every stage is
the concrete finite-stage divisorial monoid of
SourceFiniteStageModelFrobenioid: the local Frobenioid data of the stage model
is the built finite-stage reconstruction, not a new model. -/
theorem sourceStageModel_divisorMonoid_obj (stage : concreteStageBase) :
    concreteStageModel.preFrobenioid.divisorMonoid.obj stage =
      Iut.SourceFinitePlaceReconstruction.stageDivisorialAddMonoid := by
  rw [ConcreteSourceFrobenioidBridge.stageModelPreFrobenioid_divisorMonoid_eq]
  exact ConcreteSourceFrobenioidBridge.source_stage_divisorial_monoid_obj stage

/-- The local divisor group of the concrete stage model at every stage has
groupification canonically Z (the concrete finite-stage divisor equivalence). -/
theorem sourceStageModel_divisorGroupification_is_int (stage : concreteStageBase) :
    Nonempty
      (Algebra.GrothendieckAddGroup
          ((concreteStageModelDivisorialMonoid).obj stage).carrier ≃+ ℤ) :=
  ⟨Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckEquivInt⟩

/-- The concrete stage model is over the actual stage base of the concrete
Gaussian place, and every arrow of that base is epi; this is the local
Frobenioid base data shared with the concrete place of the theater carrier. -/
theorem sourceStageModel_base_data :
    CategoryTheory.IsConnected concreteStageBase ∧
    (∀ (source target : concreteStageBase) (arrow : source ⟶ target), Epi arrow) := by
  refine ⟨ConcreteSourceFrobenioidBridge.source_stage_base_connected, ?_⟩
  intro source target arrow
  exact ConcreteSourceFrobenioidBridge.source_stage_model_base_arrow_epi arrow

/-- **Local degree bridge.**  The norm-log degree of the q-parameter inside the
theater carrier's finite prime strip is minus the log of the rational prime
below the concrete place of the stage model.  The left-hand side is the local
Frobenioid degree data of the theater carrier (its prime strip is the finite
integral strip, and the selected label is 5); the right-hand side is the
rational prime of the actual place at which the concrete stage model is
realized.  This is the exact form in which the two local data are compared. -/
theorem sourceTheater_localDegree_eq_stageModel_rationalPrime
    (l : PrimeGeFive) :
    Multiplicative.toAdd
        ((finiteLocalIntegralFPrimeStrip 2 7).degree concreteInitialThetaLabel
          (finitePlaceQParameter 2 7 concreteInitialThetaLabel)) =
      - Real.log ((Rat.HeightOneSpectrum.natGenerator
          (NumberFieldFinitePlace.underlyingPrime
            (NumberFieldFinitePlace.comap (k := ℚ) concretePlace))) : ℝ) := by
  rw [finitePlaceQParameter_degree_toAdd]
  have hlabel :
      ((concreteInitialThetaLabel : FinitePrimePlace 2 7).1 : ℝ) = 5 := by
    rw [concreteInitialThetaLabel_value]
    norm_num
  rw [hlabel, concreteGaussianFivePlace_comap, concreteFivePlace_underlyingPrime,
    concreteFiveHeightOne_natGenerator]
  norm_num

/-- **Local degree bridge on the theater carrier's own prime strip.**  The same
comparison, phrased directly on sourceTheater.primeStrip: the norm-log degree of
the finite-strip q-parameter is minus the log of the rational prime below the
concrete stage-model place. -/
theorem sourceTheater_ownStripDegree_eq_stageModel_rationalPrime
    (l : PrimeGeFive) :
    Multiplicative.toAdd
        ((sourceTheater l).primeStrip.degree concreteInitialThetaLabel
          (finitePlaceQParameter 2 7 concreteInitialThetaLabel)) =
      - Real.log ((Rat.HeightOneSpectrum.natGenerator
          (NumberFieldFinitePlace.underlyingPrime
            (NumberFieldFinitePlace.comap (k := ℚ) concretePlace))) : ℝ) := by
  change Multiplicative.toAdd
      ((finiteLocalIntegralFPrimeStrip 2 7).degree concreteInitialThetaLabel
        (finitePlaceQParameter 2 7 concreteInitialThetaLabel)) = _
  exact sourceTheater_localDegree_eq_stageModel_rationalPrime l

/-! ## 3. The Example 3.6 backend/place data at the concrete place -/

/-- The actual height-one prime of the Gaussian field at which the concrete
stage model lives, as the maximal ideal of the concrete finite place. -/
def concreteHeightOneSpectrum :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers GaussianField) :=
  concretePlace.maximalIdeal

/-- The concrete place of the boundary is exactly the height-one prime used by
the Example 3.6 place data. -/
theorem boundary_place_maximalIdeal (l : PrimeGeFive) :
    (concreteSourceFrobenioidBoundary l).place.maximalIdeal =
      concreteHeightOneSpectrum :=
  rfl

/-- The concrete place lies over the rational prime 5: the restriction of the
concrete Gaussian place to Q is the checked place at 5, whose height-one prime
has natural generator 5. -/
theorem concretePlace_rationalPrime_natGenerator :
    Rat.HeightOneSpectrum.natGenerator
        (NumberFieldFinitePlace.underlyingPrime
          (NumberFieldFinitePlace.comap (k := ℚ) concretePlace)) = 5 := by
  rw [concreteGaussianFivePlace_comap, concreteFivePlace_underlyingPrime,
    concreteFiveHeightOne_natGenerator]

/-- The selected local label of the theater carrier's finite prime strip is the
rational prime 5. -/
theorem sourceTheater_selectedPlace_rationalPrime (l : PrimeGeFive) :
    (concreteInitialThetaLabel : FinitePrimePlace 2 7).1 = 5 :=
  concreteInitialThetaLabel_value

/-- **Local place agreement.**  The selected local label of the theater
carrier's finite prime strip and the rational prime below the concrete place of
the stage model coincide, both being 5. -/
theorem sourceTheater_place_agreement (l : PrimeGeFive) :
    ((concreteInitialThetaLabel : FinitePrimePlace 2 7).1 = 5) ∧
    (Rat.HeightOneSpectrum.natGenerator
        (NumberFieldFinitePlace.underlyingPrime
          (NumberFieldFinitePlace.comap (k := ℚ) concretePlace)) = 5) :=
  ⟨sourceTheater_selectedPlace_rationalPrime l, concretePlace_rationalPrime_natGenerator⟩

/-- The Example 3.6 number-field place data at the concrete place is the actual
v-adic valuation exponent of global units. -/
theorem example36PlaceData_finiteDelta_concretePlace (f : GaussianFieldˣ) :
    (numberFieldGlobalPlaceData (F := GaussianField)).finiteDelta f
        concreteHeightOneSpectrum =
      finitePlaceValueExponent concreteHeightOneSpectrum f := by
  rw [numberFieldGlobalPlaceData_finiteDelta]

/-- The Example 3.6 number-field place data at the concrete place is the actual
archimedean coordinate -log (w f) at infinite places. -/
theorem example36PlaceData_infiniteDelta_concretePlace (f : GaussianFieldˣ)
    (w : NumberField.InfinitePlace GaussianField) :
    (numberFieldGlobalPlaceData (F := GaussianField)).infiniteDelta f w =
      - Real.log (w (f : GaussianField)) := by
  rw [numberFieldGlobalPlaceData_infiniteDelta]

/-- **Divisor coordinate identification.**  The finite divisor coordinate of the
Example 3.6 model-Frobenioid divisor input (globalModelDivisor) at the concrete
place is the actual v-adic valuation exponent of global units. -/
theorem example36Backend_divisor_finite_coordinate (f : GaussianFieldˣ) :
    ((SourceModelBackend.coneGrothendieckEquiv (F := GaussianField))
        ((SourceModelBackend.globalModelDivisor (F := GaussianField))
          (Additive.ofMul f))).1 concreteHeightOneSpectrum =
      finitePlaceValueExponent concreteHeightOneSpectrum f := by
  have hglobal :
      (SourceModelBackend.globalModelDivisor (F := GaussianField))
          (Additive.ofMul f) =
        (SourceModelBackend.coneGrothendieckEquiv (F := GaussianField)).symm
          (SourceModelBackend.principalDivisorExplicit (F := GaussianField)
            (Additive.ofMul f)) :=
    rfl
  rw [hglobal, AddEquiv.apply_symm_apply]
  change (principalDivisorFinite f) concreteHeightOneSpectrum =
    finitePlaceValueExponent concreteHeightOneSpectrum f
  rw [principalDivisorFinite_apply]

/-- The archimedean divisor coordinate of the Example 3.6 model-Frobenioid
divisor input at the concrete place is -log (w f). -/
theorem example36Backend_divisor_infinite_coordinate (f : GaussianFieldˣ)
    (w : NumberField.InfinitePlace GaussianField) :
    ((SourceModelBackend.coneGrothendieckEquiv (F := GaussianField))
        ((SourceModelBackend.globalModelDivisor (F := GaussianField))
          (Additive.ofMul f))).2 w =
      - Real.log (w (f : GaussianField)) := by
  have hglobal :
      (SourceModelBackend.globalModelDivisor (F := GaussianField))
          (Additive.ofMul f) =
        (SourceModelBackend.coneGrothendieckEquiv (F := GaussianField)).symm
          (SourceModelBackend.principalDivisorExplicit (F := GaussianField)
            (Additive.ofMul f)) :=
    rfl
  rw [hglobal, AddEquiv.apply_symm_apply]
  rfl

/-- **Backend object identification.**  For the principal-divisor family the
realized backend object's divisor class, read in explicit coordinates at the
concrete place, is minus the actual v-adic valuation exponent (the frozen
backend sign convention d = -delta). -/
theorem example36BackendObject_divisor_finite_coordinate (f : GaussianFieldˣ) :
    ((SourceModelBackend.coneGrothendieckEquiv (F := GaussianField))
        ((SourceModelBackend.objectOfIdealFamily (F := GaussianField)
          (sourceModelPrincipalDivisor (numberFieldGlobalPlaceData (F := GaussianField))
            numberFieldGlobalPlaceData_hasFiniteSupport f)).divisorClass)).1
        concreteHeightOneSpectrum =
      - finitePlaceValueExponent concreteHeightOneSpectrum f := by
  change ((SourceModelBackend.coneGrothendieckEquiv (F := GaussianField))
        ((backendObject (sourceModelPrincipalDivisor
            (numberFieldGlobalPlaceData (F := GaussianField))
            numberFieldGlobalPlaceData_hasFiniteSupport f)).divisorClass)).1
        concreteHeightOneSpectrum =
      - finitePlaceValueExponent concreteHeightOneSpectrum f
  rw [backendObject_principalDivisor_divisorClass]
  change (-(principalDivisorFinite f)) concreteHeightOneSpectrum =
    - finitePlaceValueExponent concreteHeightOneSpectrum f
  rw [Finsupp.neg_apply, principalDivisorFinite_apply]

/-! ## 4. Exact obstructions: identity links and constant-q models are excluded -/

/-- **Link transport of the q-value.**  Every HodgeTheaterLink out of the
concrete carrier forces the target q-value to be the concrete q-value; a link
therefore cannot connect the carrier to a model with a different (constant or
normalized) q. -/
theorem link_target_theta_q {l : PrimeGeFive}
    {H : HodgeTheater l (FinitePrimePlace 2 7)}
    (link : HodgeTheaterLink (sourceTheater l) H) :
    H.thetaPacket.q = gaussianFiveThetaQ := by
  rw [← link.theta_q_eq, sourceTheater_theta_q]

/-- No HodgeTheaterLink out of the concrete carrier can reach any theater whose
q-value differs from the actual local q-parameter norm. -/
theorem no_link_to_theta_q_ne {l : PrimeGeFive} {q : ℝ}
    (hq : q ≠ gaussianFiveThetaQ)
    {H : HodgeTheater l (FinitePrimePlace 2 7)}
    (hH : H.thetaPacket.q = q) :
    ¬ Nonempty (HodgeTheaterLink (sourceTheater l) H) := by
  rintro ⟨link⟩
  have htarget : H.thetaPacket.q = gaussianFiveThetaQ := link_target_theta_q link
  exact hq (hH.symm.trans htarget)

/-- The concrete carrier cannot be linked to the degenerate constant-q = 1/2
finite model. -/
theorem no_link_to_constant_half_theater (l : PrimeGeFive)
    {H : HodgeTheater l (FinitePrimePlace 2 7)}
    (hH : H.thetaPacket.q = (1 / 2 : ℝ)) :
    ¬ Nonempty (HodgeTheaterLink (sourceTheater l) H) := by
  rintro ⟨link⟩
  have htarget : H.thetaPacket.q = gaussianFiveThetaQ := link_target_theta_q link
  have hhalf : (1 / 2 : ℝ) = gaussianFiveThetaQ := hH.symm.trans htarget
  rw [gaussianFiveThetaQ_eq_inv_five] at hhalf
  norm_num at hhalf

/-- The concrete carrier cannot be linked to a normalized constant-q = 1
theater. -/
theorem no_link_to_constant_one_theater (l : PrimeGeFive)
    {H : HodgeTheater l (FinitePrimePlace 2 7)}
    (hH : H.thetaPacket.q = 1) :
    ¬ Nonempty (HodgeTheaterLink (sourceTheater l) H) := by
  rintro ⟨link⟩
  have htarget : H.thetaPacket.q = gaussianFiveThetaQ := link_target_theta_q link
  have hone : (1 : ℝ) = gaussianFiveThetaQ := hH.symm.trans htarget
  rw [gaussianFiveThetaQ_eq_inv_five] at hone
  norm_num at hone

/-- **Distinct-history obstruction.**  A source Hodge-theater family is required
to have injective theater map.  If all its theaters are the single concrete
carrier, its index type is a subsingleton: the reflexive concrete history cannot
be read as a family of two or more distinct histories. -/
theorem sourceFamily_index_subsingleton_of_concrete_theater
    {l : PrimeGeFive}
    (family : SourceHodgeTheaterFamily.{0, 0, 0, 0, ui} l (FinitePrimePlace 2 7))
    (h : ∀ i, family.theater i = sourceTheater l) :
    Subsingleton family.index := by
  constructor
  intro i j
  exact family.distinct (by rw [h i, h j])

/-- **Reflexivity of the available history.**  The only history carried by the
concrete C-stage has the same carrier object as source, middle and target. -/
theorem concreteInitialThetaHistory_source_eq_middle (l : PrimeGeFive) :
    (concreteInitialThetaHistory l).source = (concreteInitialThetaHistory l).middle :=
  rfl

theorem concreteInitialThetaHistory_middle_eq_target (l : PrimeGeFive) :
    (concreteInitialThetaHistory l).middle = (concreteInitialThetaHistory l).target :=
  rfl

/-- The history's theater is the finite integral test theater
(concreteInitialThetaHodgeTheater), not a distinct source theater. -/
theorem concreteInitialThetaHistory_source_theater (l : PrimeGeFive) :
    (concreteInitialThetaHistory l).source.theater =
      concreteInitialThetaHodgeTheater l :=
  rfl

/-- The prime-strip arrow of the available history is the identity
prime-strip equality: the history carries no non-identity prime-strip
transport. -/
theorem concreteInitialThetaHistory_primeStrip_identity (l : PrimeGeFive) :
    (concreteInitialThetaHistory l).source_to_middle =
      (rfl : (concreteInitialThetaHistory l).source.theater.primeStrip =
        (concreteInitialThetaHistory l).middle.theater.primeStrip) :=
  rfl

/-- The available history's theta q-value is the same actual q-value, so the
history records only q-preservation, not the paper's theta-link. -/
theorem concreteInitialThetaHistory_theta_q (l : PrimeGeFive) :
    (concreteInitialThetaHistory l).source.theater.thetaPacket.q =
      gaussianFiveThetaQ :=
  concreteInitialThetaHodgeTheater_q l

/-! ## 5. Consumer-facing summary -/

/-- **Summary of the carrier/backend identification.**  The concrete source
Hodge-theater carrier is built from the actual Gaussian initial Theta data and
the actual local q-parameter; the concrete Frobenioid boundary is its boundary
(the same C-stage), with the concrete stage model as its Frobenioid
presentation; the concrete place of both is the Gaussian place above the
rational prime 5, which is also the selected local label of the finite prime
strip. -/
theorem sourceTheaterCarrier_identification_summary (l : PrimeGeFive) :
    (sourceTheater l).arithmetic = concreteGaussianInitialThetaArithmeticData l ∧
    (sourceTheater l).thetaPacket.q = gaussianFiveThetaQ ∧
    gaussianFiveThetaQ = (5 : ℝ)⁻¹ ∧
    (concreteSourceFrobenioidBoundary l).cStage.theater = sourceTheater l ∧
    (concreteSourceFrobenioidBoundary l).place = concretePlace ∧
    (concreteSourceFrobenioidBoundary l).model = concreteStageModel ∧
    (concreteSourceFrobenioidBoundary l).model_input = concreteStageModelInput ∧
    (Rat.HeightOneSpectrum.natGenerator
        (NumberFieldFinitePlace.underlyingPrime
          (NumberFieldFinitePlace.comap (k := ℚ) concretePlace)) = 5) ∧
    ((concreteInitialThetaLabel : FinitePrimePlace 2 7).1 = 5) := by
  refine ⟨sourceTheater_arithmetic l, sourceTheater_theta_q l,
    gaussianFiveThetaQ_eq_inv_five, rfl, rfl, rfl, rfl,
    concretePlace_rationalPrime_natGenerator, sourceTheater_selectedPlace_rationalPrime l⟩

end
end SourceTheaterCarrier
end Example36
end Frobenioid
end IUTII
end IUT
end LeanFormal

namespace LeanFormal.IUT.Audit

/-- Audit record for the concrete source Hodge-theater carrier of the Gaussian
C-stage and its identification with the concrete stage-model Frobenioid backend
at the Example 3.6 place.  The carrier, the backend identification, the place
data identification and the exact obstructions are proved; the source theta
generators, the anabelian links/distinct histories and the stage-model
valuation normalization bridge are NOT constructed. -/
def example36SourceTheaterCarrier : Obligation :=
  { id := "IUT-I-II.example36-source-theater-carrier"
    source :=
      "IUT I, Definition 3.1 and Sections 4-5 (initial Theta data, Hodge " ++
        "theaters, histories and links); IUT II, Definition 4.9(i) (local " ++
        "integral F-prime strip); IUT III, Example 3.6 (finite-stage model " ++
        "Frobenioid and number-field place data)"
    status := VerificationStatus.interface
    note :=
      "Constructed sourceTheater, the Hodge theater of the actual Gaussian " ++
        "C-stage: actual Q(i) initial Theta arithmetic with the base-changed " ++
        "split multiplicative curve, the actual nonzero integral-closure " ++
        "F-prime strip finiteLocalIntegralFPrimeStrip 2 7, and the actual " ++
        "finite theta packet with q = gaussianFiveThetaQ = 1/5 " ++
        "(sourceTheater_theta_q_eq_inv_five). Proved the concrete " ++
        "source-Frobenioid boundary is the boundary of the same C-stage: " ++
        "theater = sourceTheater, place = concretePlace, model = " ++
        "concreteStageModel, model_input = concreteStageModelInput, local " ++
        "Kummer kernel = zmultiples l " ++
        "(sourceTheater_stageModel_provenance), and the stage model's " ++
        "divisorial monoid object is the concrete finite-stage divisorial " ++
        "monoid with groupification Z (sourceStageModel_divisorMonoid_obj, " ++
        "sourceStageModel_divisorGroupification_is_int). Identified the " ++
        "Example 3.6 number-field place data, the model-Frobenioid divisor " ++
        "input and the realized backend object at the concrete place with " ++
        "the actual v-adic valuation exponent " ++
        "(example36PlaceData_finiteDelta_concretePlace, " ++
        "example36Backend_divisor_finite_coordinate, " ++
        "example36BackendObject_divisor_finite_coordinate), and proved the " ++
        "concrete place lies above the rational prime 5, the same prime as " ++
        "the finite strip's selected label " ++
        "(sourceTheater_place_agreement). Exact obstructions: every " ++
        "HodgeTheaterLink transports the concrete q-value, so no link reaches " ++
        "a constant-q = 1/2 or q = 1 model (no_link_to_theta_q_ne, " ++
        "no_link_to_constant_half_theater, no_link_to_constant_one_theater); " ++
        "a source family all of whose theaters are the single concrete " ++
        "carrier has subsingleton index " ++
        "(sourceFamily_index_subsingleton_of_concrete_theater); the only " ++
        "history carried by the concrete C-stage is reflexive with identity " ++
        "prime-strip arrow (concreteInitialThetaHistory_*). NOT proved: the " ++
        "actual place-indexed prime strip over the Gaussian field, the source " ++
        "theta generators, the anabelian theta-/log-links and distinct " ++
        "histories, and the identification of the stage-model normalized " ++
        "valuation with the Example 3.6 valuation on global units. None of " ++
        "these is assumed as a field; no theta-pilot/q-pilot/Tate " ++
        "identification is claimed."
    dependsOn :=
      [ "IUT-I-II.concrete-source-frobenioid-bridge",
        "IUT-I-II.concrete-initial-theta-c-stage",
        "IUT-II.local-integral-f-prime-strip-carrier",
        "IUT-II.local-integral-monoid-carrier",
        "IUT-I-II.prime-strips-frobenioids",
        "IUT-I-II.source-finite-stage-model-frobenioid",
        "IUT-I.hodge-theater-carrier-and-links" ] }

end LeanFormal.IUT.Audit
