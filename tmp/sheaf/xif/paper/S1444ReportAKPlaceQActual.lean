import tmp.sheaf.xif.paper.S605KSideQVActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4FKDescentBridge
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# S1444 (route A): the q comparison at the source-designated K-place

Source pointers.  IUT I, Definition 3.1(b),(c),(e) and Example 3.2(iv)
(corpus lines 3142--3184, 3216--3226, 3701--3726): the bad moduli set
V^bad_mod is a set of nonarchimedean valuations of F_mod; the restriction
section V(K) -> V_mod selects one K-place above each moduli place; q_v is the
local parameter at the section-selected K-place, and its 2l-th root is taken in
the completion K_v, determined only up to a mu_{2l}-multiple.

Route A of coord/reports/gap-exploration-20261030.md asks for the following
finite deliverable: on the K-place that the *source section* designates (not on
an independently chosen Classical.choose place), build the q parameter
comparison with the F-side source parameter, and record which fields are
supplied by existing proof bodies and which remain genuine obligations.

What is built here:

* the actual F-place sectionFPlace (the A.F-shadow of the section lift) and the
  designated K-place sectionKPlace (Definition 3.1(e) section lift), with
  sectionKPlace_comap and sectionKPlace_comap_fmod;
* the actual F-side q parameter sectionFQ obtained by *instantiating clause (b)
  at the section F-place* (so no equality of Classical.choose places is needed),
  with the F-side Tate comparison supplied by clause (b) and the clause-(c)
  coprimality of its order;
* the K-side q parameter sectionQ, defined as the actual completionMap image of
  sectionFQ at sectionKPlace; its q-value equality sectionQ_q is definitional,
  and its order/valuation/exponent laws are supplied by
  FinitePlaceQCandidate.order_map, valuation_map, exponent_map, with the
  ramification index identified as fkDescentSectionRamificationIndex;
* the valuation/norm normalization: the canonical completion norm and log
  magnitude scale by e * f (sectionQ_norm, sectionQ_localLogMagnitude,
  sectionQ_localSignedLog, section_residueNormBase_eq,
  section_completionNormDegree_eq), while the order-normalized reading scales
  by e alone (sectionQ_orderNormalizedMagnitude,
  sectionQ_orderNormalizedMagnitude_eq);
* the clause-(c) inputs of the root chain: the kernel-field identification with
  the E[l]-kernel field, the range condition, and the K-side l-torsion basis
  with its transport law;
* the exact S605 interface: the first field of
  S605KSideQVActual.KSideQVComparisonData isolated as the named proposition
  KSideQVFirstField; the proof that S605's shadow field is implied by the first
  field (place_eq_imp_shadow_eq), so S605's five-field gate is repackaged
  without loss as the residual KSideQRouteAResidual = (first field, K-side q
  section with its defining equation, K-side Tate uniformization, order law);
  the equivalence kSideQVComparisonRequired_iff_residual; and S605's consumer
  constructors (KSideQVFamilySpec, KSideQVFamilyRequired, KSideQVExactGap)
  re-derived in that shape;
* the exact root-descent obligation at the designated K-place
  (SectionKPlaceTwoLRoot), its 2l-order law, its l | e necessary condition
  (sectionQ_twoLRoot_l_dvd_ramification), and the mu_{2l} indeterminacy of two
  roots (Example 3.2(iv)).

Obligation table.

  F-place over the bad moduli place ....... fkDescentShadow + _comap; proved
  designated K-place and comap ........... sectionFiniteLift + _comap; proved
  F-side q and its Tate comparison ....... clause (b) witness at sectionFPlace;
                                           supplied by the source input T
  K-side q via completionMap ............. FinitePlaceQCandidate.map; proved
  order scaling ord_K = e * ord_F ........ order_map; proved
  valuation scaling v_K = v_F ^ e ........ valuation_map; proved
  norm scaling e*f (canonical) / e ....... ArithmeticQPilotBaseChange; proved
  kernel field / K-side l-torsion basis .. clause (c); supplied by T
  K-side Tate uniformization ............. NOT available; obligation
  S605 first field ....................... NOT derivable; named obligation
  S605 shadow field ...................... implied by the first field; proved
  2l-th root of q_v in K_v ............... NOT available; obligation

No sorry, no new axiom, no FinalXiF wrapper, no inequality, no shrinking of
the paper's quantifiers.  This file does not close Corollary 3.12.

Note on S618.  tmp/sheaf/xif/paper/S618KSideQVPlaceActual.lean is not imported
here: as of this writing it does not compile (it does not open
QPilotZeroLocusDivisorActual, so qVFamily is unknown, and its rw [<- hplace]
at line 38 does not find kSidePlace T b after the change).  Its two relevant
relevant statement is therefore restated below (place_eq_imp_shadow_eq); it
coincides with S618's content once that file is repaired.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.S605KSideQVActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. The actual F-place and the designated K-place -/

/-- The actual F-place attached to the source section at the bad moduli place
b: the A.F-shadow of the section-chosen K-place.  This is the F-place that the
paper's q_v at the designated K-place actually sits over. -/
abbrev sectionFPlace : NumberField.FinitePlace T.arithmetic.F :=
  fkDescentShadow (nativePlaceSelection T) b.1

/-- The K-place designated by the source section (IUT I, Definition 3.1(e)),
i.e. the section lift of the bad moduli place b. -/
abbrev sectionKPlace : NumberField.FinitePlace T.arithmetic.K :=
  kSidePlace (T := T) b

/-- The designated K-place lies over the actual F-place by construction. -/
theorem sectionKPlace_comap :
    NumberFieldFinitePlace.comap (k := T.arithmetic.F) (sectionKPlace T b) =
      sectionFPlace T b :=
  rfl

/-- The actual F-place still lies over the original bad moduli place. -/
theorem sectionFPlace_comap :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (sectionFPlace T b) =
      b.1 :=
  fkDescentShadow_comap (nativePlaceSelection T) b.1

/-- The designated K-place lies over the bad moduli place b as well. -/
theorem sectionKPlace_comap_fmod :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (sectionKPlace T b) =
      b.1 :=
  sectionFiniteLift_comap (nativePlaceSelection T) b.1

/-- Membership of the actual F-place in the source bad moduli set. -/
theorem sectionFPlace_mem_bad :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (sectionFPlace T b) ∈
      (nativePlaceSelection T).V_mod_bad := by
  rw [sectionFPlace_comap (T := T) (b := b)]
  exact b.2

/-! ## 2. The F-side source q parameter, instantiated at the section place

qVFamily (S438 and QPilotZeroLocusDivisorActual) instantiates clause (b) at the
independently chosen place (nativeBadLift T).lift b.  Route A instead
instantiates the *same* clause-(b) comparison at the F-place that the source
section actually uses, so no identity between two Classical.choose places is
needed for this half of the diagram. -/

/-- Clause (b)'s actual Tate comparison witness at the section F-place. -/
noncomputable def sectionTateWitness :
    SourceTateComparisonWitness T.arithmetic (sectionFPlace T b) :=
  Classical.choice
    (T.clauseB.q_comparison (sectionFPlace T b) (sectionFPlace_mem_bad T b))

/-- The actual F-side q parameter of clause (b) at the section F-place. -/
noncomputable def sectionFQ : FinitePlaceQCandidate (sectionFPlace T b) :=
  (sectionTateWitness T b).parameter

/-- The F-side parameter is the clause-(b) comparison parameter. -/
theorem sectionFQ_eq_comparisonParameter :
    sectionFQ T b =
      (Classical.choice
        (T.clauseB.q_comparison (sectionFPlace T b)
          (sectionFPlace_mem_bad T b))).parameter :=
  rfl

/-- Clause (b)'s Tate uniformization at the section F-place: supplied by the
source input, not proved here. -/
noncomputable def sectionTateWitness_comparison :
    TateCurveComparison T.arithmetic.curve (sectionFPlace T b) (sectionFQ T b) :=
  (sectionTateWitness T b).comparison

/-- The source condition of Definition 3.1(c): the F-side order is prime to l. -/
theorem sectionFQ_order_coprime : Nat.Coprime (sectionFQ T b).order l.value :=
  (sectionTateWitness T b).order_coprime

/-! ## 3. The K-side q parameter via the actual completionMap -/

/-- The K-side q parameter at the designated K-place: the actual completionMap
image of the F-side clause-(b) parameter.  The paper's q_v at K_v is this
transported parameter, not the F-side parameter itself. -/
noncomputable def sectionQ : FinitePlaceQCandidate (sectionKPlace T b) :=
  FinitePlaceQCandidate.map (k := T.arithmetic.F) (sectionKPlace T b) (sectionFQ T b)

/-- The q-value equality: q_K is literally the completionMap of q_F.  This is
the q equation of the route-A diagram (definitional). -/
theorem sectionQ_q :
    (sectionQ T b).q =
      completionMap (k := T.arithmetic.F) (sectionKPlace T b) (sectionFQ T b).q :=
  FinitePlaceQCandidate.map_q (k := T.arithmetic.F) (sectionKPlace T b) (sectionFQ T b)

/-- The ramification index of the designated K-place over the actual F-place is
the section ramification index of the source. -/
theorem sectionRamificationIndex_eq :
    (NumberFieldFinitePlace.comap (k := T.arithmetic.F) (sectionKPlace T b)).maximalIdeal.asIdeal.ramificationIdx'
        (sectionKPlace T b).maximalIdeal.asIdeal =
      fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 :=
  rfl

/-- The same identification for the local ramification index used by
ArithmeticQPilotBaseChange. -/
theorem sectionLocalRamificationIndex_eq :
    ArithmeticQPilotBaseChange.localRamificationIndex (k := T.arithmetic.F) (sectionKPlace T b) =
      fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 :=
  rfl

/-- Order scaling at the designated places: ord_K(q_K) = e * ord_F(q_F)
(S438's order law at the section pair). -/
theorem sectionQ_order :
    (sectionQ T b).order =
      fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 *
        (sectionFQ T b).order :=
  FinitePlaceQCandidate.order_map (k := T.arithmetic.F) (sectionKPlace T b) (sectionFQ T b)

/-- The same order scaling with the local ramification index. -/
theorem sectionQ_order' :
    (sectionQ T b).order =
      ArithmeticQPilotBaseChange.localRamificationIndex (k := T.arithmetic.F) (sectionKPlace T b) *
        (sectionFQ T b).order := by
  rw [sectionQ_order, ← sectionLocalRamificationIndex_eq (T := T) (b := b)]

/-! ## 4. Valuation and norm normalization

Two readings must be kept apart (see the gap report, section on norm versus
coefficient):

* the canonical completion norm and logarithmic magnitude scale by e * f;
* the order-normalized magnitude (division by the residue logarithm) recovers
  the discrete order and scales by e alone.

Both are instantiations of ArithmeticQPilotBaseChange at the section pair. -/

/-- Valuation scaling: v_K(q_K) = v_F(q_F) ^ e. -/
theorem sectionQ_valuation :
    (Valued.v (sectionQ T b).q : WithZero (Multiplicative Int)) =
      (Valued.v (sectionFQ T b).q : WithZero (Multiplicative Int)) ^
        ArithmeticQPilotBaseChange.localRamificationIndex (k := T.arithmetic.F) (sectionKPlace T b) :=
  FinitePlaceQCandidate.valuation_map (k := T.arithmetic.F) (sectionKPlace T b)
    (sectionFQ T b)

/-- Integer-exponent scaling: exp_K = e * exp_F. -/
theorem sectionQ_exponent :
    (sectionQ T b).exponent =
      (ArithmeticQPilotBaseChange.localRamificationIndex (k := T.arithmetic.F) (sectionKPlace T b) : Int) *
        (sectionFQ T b).exponent :=
  FinitePlaceQCandidate.exponent_map (k := T.arithmetic.F) (sectionKPlace T b)
    (sectionFQ T b)

/-- Canonical completion norm: ||q_K|| = ||q_F|| ^ (e * f). -/
theorem sectionQ_norm :
    ‖(sectionQ T b).q‖ =
      ‖(sectionFQ T b).q‖ ^
        ArithmeticQPilotBaseChange.completionNormDegree (k := T.arithmetic.F)
          (sectionKPlace T b) :=
  ArithmeticQPilotBaseChange.qNorm_map (k := T.arithmetic.F) (sectionKPlace T b)
    (sectionFQ T b)

/-- The canonical norm written with the actual residue norm of the place. -/
theorem sectionQ_norm_eq_residueNormBase_zpow :
    ‖(sectionQ T b).q‖ =
      ArithmeticQPilotBaseChange.residueNormBase (sectionKPlace T b) ^ (-(sectionQ T b).exponent) :=
  ArithmeticQPilotBaseChange.qNorm_eq_residueNormBase_zpow (parameter := sectionQ T b)

/-- Canonical logarithmic magnitude scales by e * f. -/
theorem sectionQ_localLogMagnitude :
    localLogMagnitude (sectionQ T b) =
      (ArithmeticQPilotBaseChange.completionNormDegree (k := T.arithmetic.F)
        (sectionKPlace T b) : ℝ) *
        localLogMagnitude (sectionFQ T b) :=
  ArithmeticQPilotBaseChange.localLogMagnitude_map (k := T.arithmetic.F)
    (sectionKPlace T b) (sectionFQ T b)

/-- Signed logarithmic reading scales by e * f. -/
theorem sectionQ_localSignedLog :
    localSignedLog (sectionQ T b) =
      (ArithmeticQPilotBaseChange.completionNormDegree (k := T.arithmetic.F)
        (sectionKPlace T b) : ℝ) *
        localSignedLog (sectionFQ T b) :=
  ArithmeticQPilotBaseChange.localSignedLog_map (k := T.arithmetic.F)
    (sectionKPlace T b) (sectionFQ T b)

/-- Order-normalized magnitude scales by e alone. -/
theorem sectionQ_orderNormalizedMagnitude :
    orderNormalizedMagnitude (sectionQ T b) =
      (ArithmeticQPilotBaseChange.localRamificationIndex (k := T.arithmetic.F) (sectionKPlace T b) : ℝ) *
        orderNormalizedMagnitude (sectionFQ T b) :=
  ArithmeticQPilotBaseChange.orderNormalizedMagnitude_map (k := T.arithmetic.F)
    (sectionKPlace T b) (sectionFQ T b)

/-- The order-normalized reading of the K-side parameter is e times the source
F-side order. -/
theorem sectionQ_orderNormalizedMagnitude_eq :
    orderNormalizedMagnitude (sectionQ T b) =
      (fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 : ℝ) *
        ((sectionFQ T b).order : ℝ) := by
  rw [sectionQ_orderNormalizedMagnitude, orderNormalizedMagnitude_eq_order,
    sectionLocalRamificationIndex_eq (T := T) (b := b)]

/-- Residue norm base at the designated K-place is the f-th power of the base
at the actual F-place. -/
theorem section_residueNormBase_eq :
    ArithmeticQPilotBaseChange.residueNormBase (sectionKPlace T b) =
      ArithmeticQPilotBaseChange.residueNormBase (sectionFPlace T b) ^
        ArithmeticQPilotBaseChange.localResidueDegree (k := T.arithmetic.F) (sectionKPlace T b) :=
  ArithmeticQPilotBaseChange.residueNormBase_eq_lower_pow (k := T.arithmetic.F)
    (sectionKPlace T b)

/-- The norm degree is e * f with the section ramification index. -/
theorem section_completionNormDegree_eq :
    ArithmeticQPilotBaseChange.completionNormDegree (k := T.arithmetic.F)
      (sectionKPlace T b) =
      fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 *
        ArithmeticQPilotBaseChange.localResidueDegree (k := T.arithmetic.F) (sectionKPlace T b) := by
  rw [show ArithmeticQPilotBaseChange.completionNormDegree (k := T.arithmetic.F) (sectionKPlace T b) =
      ArithmeticQPilotBaseChange.localRamificationIndex (k := T.arithmetic.F) (sectionKPlace T b) *
        ArithmeticQPilotBaseChange.localResidueDegree (k := T.arithmetic.F) (sectionKPlace T b) from rfl,
    sectionLocalRamificationIndex_eq (T := T) (b := b)]

/-! ## 5. The clause-(c) inputs of the root chain

Clause (c) identifies the source field K with the mod-l torsion kernel field
and provides the K-side l-torsion basis together with its transport to the
F-side basis.  These are the source-level carriers on which q_v^(1/2l) and its
mu_{2l} indeterminacy live. -/

/-- Clause (c): the kernel-field identification K = E[l]-kernel field. -/
noncomputable def sectionKernelFieldIdentification_spec :
    T.arithmetic.K ≃ₐ[T.arithmetic.F]
      T.arithmetic.curve.galoisLTorsionKernelField l T.clauseC.torsion_basis :=
  T.clauseC.kernel_field_identification

/-- Clause (c): the range of the identification is exactly the kernel field. -/
theorem sectionKernelFieldIdentification_range :
    Set.range (fun x : T.arithmetic.K =>
      (T.clauseC.kernel_field_identification x : AlgebraicClosure T.arithmetic.F)) =
      (T.arithmetic.curve.galoisLTorsionKernelField l T.clauseC.torsion_basis :
        Set (AlgebraicClosure T.arithmetic.F)) :=
  SourceClauseC.kernel_field_range_spec T.clauseC

/-- Clause (c): the source-supplied K-side l-torsion basis. -/
noncomputable def sectionKTorsionBasis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      (T.arithmetic.curve.baseChange T.arithmetic.K).LTorsion l :=
  SourceClauseC.k_torsion_basis T.clauseC

/-- Clause (c): the K-side basis transports to the F-side basis. -/
theorem sectionKTorsionBasis_transport_eq :
    (sectionKTorsionBasis T).trans (SourceClauseC.k_to_f_torsion_transport T.clauseC) =
      T.clauseC.torsion_basis :=
  SourceClauseC.k_torsion_basis_transport_eq_f_torsion_basis T.clauseC

/-! ## 6. The exact root descent at the designated K-place

IUT I, Example 3.2(iv): q_v^(1/2l) is taken in the completion K_v.  The
following proposition is the exact obligation *at the section place*; it is not
assumed anywhere in this file, and it is not derived from clause (c) alone
(clause (c) is a mod-l torsion statement, whereas the root is a Kummer
condition modulo 2l in the completion K_v). -/

/-- The exact source root-descent obligation at the designated K-place: a
nonzero 2l-th root of q_v inside Completion (sectionKPlace T b). -/
def SectionKPlaceTwoLRoot : Prop :=
  Nonempty (QParameterTwoLRootCard l (sectionKPlace T b) (sectionQ T b))

/-- The 2l-order law of a root: (2l) * ord(root) = ord_K(q_v). -/
theorem sectionQ_twoLRoot_order_eq
    (card : QParameterTwoLRootCard l (sectionKPlace T b) (sectionQ T b)) :
    (2 * l.value) * card.toQCandidate.order = (sectionQ T b).order :=
  twoLRootCard_parameter_order_eq card

/-- 2l divides the order of q_v at the designated K-place. -/
theorem sectionQ_twoLRoot_twoL_dvd_order
    (card : QParameterTwoLRootCard l (sectionKPlace T b) (sectionQ T b)) :
    (2 * l.value) ∣ (sectionQ T b).order :=
  twoLRootCard_twoL_dvd_parameter_order card

/-- Normalized form of the order law: (2l) * ord(root) = e * ord_F(q_F). -/
theorem sectionQ_twoLRoot_order_eq_ramification
    (card : QParameterTwoLRootCard l (sectionKPlace T b) (sectionQ T b)) :
    (2 * l.value) * card.toQCandidate.order =
      fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 *
        (sectionFQ T b).order := by
  rw [sectionQ_twoLRoot_order_eq, sectionQ_order]

/-- The exact arithmetic consequence: a 2l-th root at the designated K-place
forces l to divide the section ramification index.  This is where the F-side
coprimality of Definition 3.1(c) is consumed: it does not obstruct a K-side
root, because the obstruction is transported to l | e.  S342 excludes a root in
the completed F-place itself, where the local order is the source order and
2l | ord_F(q_F) contradicts l being prime to ord_F(q_F). -/
theorem sectionQ_twoLRoot_l_dvd_ramification
    (card : QParameterTwoLRootCard l (sectionKPlace T b) (sectionQ T b)) :
    l.value ∣ fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 := by
  have hdvd : l.value ∣ (sectionQ T b).order :=
    twoLRootCard_l_dvd_parameter_order card
  rw [sectionQ_order] at hdvd
  exact ((sectionFQ_order_coprime T b).symm.dvd_mul_right).mp hdvd

/-- The mu_{2l} indeterminacy of Example 3.2(iv): two 2l-th roots of the same
K-side q differ by a 2l-th root of unity.  This is the legal equivalence
between two choices of q_v^(1/2l). -/
theorem sectionQ_twoLRoot_ratio_pow_eq_one
    {r₁ r₂ : Completion (sectionKPlace T b)}
    (h₁ : r₁ ^ (2 * l.value) = (sectionQ T b).q)
    (h₂ : r₂ ^ (2 * l.value) = (sectionQ T b).q) :
    (r₁ / r₂) ^ (2 * l.value) = 1 :=
  twoLRoot_ratio_pow_eq_one (sectionQ T b).q_ne_zero h₁ h₂

/-- Unit form of the same indeterminacy: two rooted candidates at the
designated place differ by a 2l-th root of unity. -/
theorem sectionQ_twoLRoot_ratio_mem_rootsOfUnity
    {r₁ r₂ : (Completion (sectionKPlace T b))ˣ}
    (h₁ : r₁ ^ (2 * l.value) = Units.mk0 (sectionQ T b).q (sectionQ T b).q_ne_zero)
    (h₂ : r₂ ^ (2 * l.value) = Units.mk0 (sectionQ T b).q (sectionQ T b).q_ne_zero) :
    r₁ / r₂ ∈ rootsOfUnity (2 * l.value) (Completion (sectionKPlace T b)) :=
  twoLRootUnit_ratio_mem_rootsOfUnity h₁ h₂

/-! ## 7. The exact S605 interface: first field, redundant shadow, residual

S605KSideQVActual.KSideQVComparisonData has five fields.  The first field is
isolated below as the named proposition KSideQVFirstField; it compares two
independent Classical.choose places (qVFamilyKLift from comap_surjective and
sectionFiniteLift from the source section) and is not derivable from the rest of
the source data.  Route A does not need it: sections 1--6 build the same
comparison directly at the designated place.

What is derivable is the *shadow* field: the K-place identity implies the
F-place identity (place_eq_imp_shadow_eq), so S605's shadow_eq field is
redundant given place_eq.  The residual record below therefore records S605's
gate in the form actually needed by its consumers: the first field, the K-side
q section with its defining equation, the K-side Tate uniformization, and the
order law.  Equivalence with S605's structure is pure repackaging
(kSideQVComparisonRequired_iff_residual); the consumer constructors of S605 are
then re-derived in this shape.

Tooling note (not a mathematical gap).  Deriving the residual's order_eq field
from S438's order law requires computing .order of the Eq.rec-cast candidate
place_eq.symm ▸ qVFamilyK; that identification is definitionally the identity on
data, but the current elaborator hits a whnf heartbeat timeout on it in this
import context, so the field is kept explicit here instead of being claimed as
proved.  The corresponding order law at the source-designated place *is* proved
above (sectionQ_order), which is the content route A actually needs. -/

/-- The exact first field of S605's KSideQVComparisonData. -/
def KSideQVFirstField : Prop :=
  qVFamilyKLift T b = kSidePlace (T := T) b

/-- S618's bridge, restated: the K-place identity forces the F-place identity of
the shadow.  (S618 does not currently compile; see the file header.) -/
theorem place_eq_imp_shadow_eq
    (hplace : qVFamilyKLift T b = kSidePlace (T := T) b) :
    sectionFPlace T b = (nativeBadLift T).lift b := by
  have h := qVFamilyKLift_comap (T := T) (b := b)
  rw [hplace] at h
  exact h

/-- S605's gate in the route-A shape: the exact first field, the K-side q
section with its defining equation, the K-side Tate uniformization, and the
order law.  The shadow field of S605 is omitted because it is implied by
place_eq (place_eq_imp_shadow_eq). -/
structure KSideQRouteAResidual where
  /-- The exact first field of KSideQVComparisonData. -/
  place_eq : qVFamilyKLift T b = kSidePlace (T := T) b
  /-- The K-side q section at the source-designated place. -/
  qSection : FinitePlaceQCandidate (kSidePlace (T := T) b)
  /-- Its defining equation inside S605's structure. -/
  qSection_eq : qSection = place_eq.symm ▸ qVFamilyK T b
  /-- The K-side Tate uniformization at the source-designated place. -/
  uniformization : TateCurveComparison (kSideCurve (T := T))
    (kSidePlace (T := T) b) qSection
  /-- The order law required by S605. -/
  order_eq : qSection.order =
    fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 *
      (qVFamily T b).order

/-- From S605's gate to the route-A residual: pure repackaging, using that the
shadow field is implied by the place identity. -/
noncomputable def residualOfComparisonData
    (G : KSideQVComparisonData (T := T) (b := b)) :
    KSideQRouteAResidual T b where
  place_eq := G.place_eq
  qSection := G.qSection
  qSection_eq := G.qSection_eq
  uniformization := G.uniformization
  order_eq := G.order_eq

/-- From the route-A residual back to S605's gate. -/
noncomputable def comparisonDataOfResidual
    (R : KSideQRouteAResidual T b) :
    KSideQVComparisonData (T := T) (b := b) where
  place_eq := R.place_eq
  shadow_eq := place_eq_imp_shadow_eq (T := T) (b := b) R.place_eq
  qSection := R.qSection
  qSection_eq := R.qSection_eq
  uniformization := R.uniformization
  order_eq := R.order_eq

/-- S605's gate is exactly the route-A residual. -/
theorem kSideQVComparisonRequired_iff_residual :
    KSideQVComparisonRequired (T := T) (b := b) ↔
      Nonempty (KSideQRouteAResidual T b) :=
  ⟨fun ⟨G⟩ => ⟨residualOfComparisonData T b G⟩,
   fun ⟨R⟩ => ⟨comparisonDataOfResidual T b R⟩⟩

/-- The first field is forced by S605's gate. -/
theorem firstField_of_comparisonRequired
    (h : KSideQVComparisonRequired (T := T) (b := b)) :
    KSideQVFirstField T b := by
  obtain ⟨G⟩ := h
  exact G.place_eq

/-- The first field is forced by an inhabitant of S605's structure. -/
theorem firstField_of_comparisonData
    (G : KSideQVComparisonData (T := T) (b := b)) :
    KSideQVFirstField T b :=
  G.place_eq

/-- S605's gate also forces the actual F-place of the section diagram to be the
independently chosen nativeBadLift place. -/
theorem sectionFPlace_eq_of_comparisonRequired
    (h : KSideQVComparisonRequired (T := T) (b := b)) :
    sectionFPlace T b = (nativeBadLift T).lift b := by
  obtain ⟨G⟩ := h
  exact G.shadow_eq

/-- Consumer of S605: from the route-A residual, the paper's K-side q object
KSideQVFamilySpec exists. -/
noncomputable def kSideQVFamilySpecOfRouteA
    (R : KSideQRouteAResidual T b) :
    KSideQVFamilySpec (T := T) (b := b) :=
  kSideQVFamilySpecOfComparison (T := T) (b := b)
    (comparisonDataOfResidual T b R)

/-- Consumer of S605: KSideQVFamilyRequired from the route-A residual. -/
theorem kSideQVFamilyRequired_of_routeA
    (R : KSideQRouteAResidual T b) :
    KSideQVFamilyRequired (T := T) (b := b) :=
  kSideQVFamilyRequired_of_comparison (T := T) (b := b)
    (comparisonDataOfResidual T b R)

/-- The named exact gap of S605, inhabited from the route-A residual. -/
theorem kSideQVExactGap_of_routeA
    (R : KSideQRouteAResidual T b) :
    KSideQVExactGap (T := T) (b := b) :=
  ⟨comparisonDataOfResidual T b R⟩

/-! ## 8. The assembled route-A diagram -/

/-- The section-place q comparison assembled as data at the source-designated
places: the actual F-place with its comap relation, the F-side clause-(b)
parameter, the K-side completionMap parameter, the q equation, and the order
law.  This is the object that S605-style consumers can use without any identity
between independent Classical.choose places. -/
structure SectionKPlaceQDiagram where
  comap_eq : NumberFieldFinitePlace.comap (k := T.arithmetic.F) (sectionKPlace T b) =
    sectionFPlace T b
  qF : FinitePlaceQCandidate (sectionFPlace T b)
  qK : FinitePlaceQCandidate (sectionKPlace T b)
  qK_q : qK.q = completionMap (k := T.arithmetic.F) (sectionKPlace T b) qF.q
  qK_order : qK.order = fkDescentSectionRamificationIndex
    (nativePlaceSelection T) b.1 * qF.order

/-- The assembled route-A diagram at the source-designated K-place. -/
noncomputable def sectionKPlaceQDiagram : SectionKPlaceQDiagram T b where
  comap_eq := sectionKPlace_comap (T := T) (b := b)
  qF := sectionFQ T b
  qK := sectionQ T b
  qK_q := sectionQ_q (T := T) (b := b)
  qK_order := sectionQ_order (T := T) (b := b)

end LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual