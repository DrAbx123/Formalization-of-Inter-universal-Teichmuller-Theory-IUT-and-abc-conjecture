import LeanFormal.IUTDispute

/-!
  Diagnostic for the extra identifications in the Scholze--Stix-style
  simplification.  This is deliberately separate from the source-facing IUT
  interfaces: it records an ordered space, a volume readout, and the extra
  endpoint/tightness assumptions used by the criticism model.

  The final witness keeps the scalar normalization and the lower hull bound,
  but drops the upper tightness bound and the qPilot = thetaPilot
  identification.  Thus the tight-collapse theorem is conditional on those
  extra assumptions, not a contradiction theorem for a general IUT model.
-/

namespace LeanFormal.IUTDisputeSimplification

open LeanFormal.IUTDispute

/-! ## The decomposed tight critic model -/

structure TightCriticData where
  Omega : Type
  [ord : PartialOrder Omega]
  vol : Omega -> Real
  vol_mono : Monotone vol
  qPilot : Omega
  thetaPilot : Omega
  hull : Omega
  qPilot_eq_thetaPilot : qPilot = thetaPilot
  qPilot_le_hull : qPilot <= hull
  hull_le_thetaPilot : hull <= thetaPilot
  q : Real
  theta : Real
  hullValue : Real
  q_read : vol qPilot = q
  theta_read : vol thetaPilot = theta
  hull_read : vol hull = hullValue
  q_negative : q < 0
  factor : Real
  factor_gt_one : 1 < factor
  theta_eq_factor_q : theta = factor * q

attribute [instance] TightCriticData.ord

/-- The same ordered-space and tight-hull assumptions give the two-sided
    scalar chain q <= hull <= theta. -/
theorem tight_hull_value_chain (D : TightCriticData) :
    D.q <= D.hullValue /\ D.hullValue <= D.theta := by
  constructor
  · calc
      D.q = D.vol D.qPilot := D.q_read.symm
      _ <= D.vol D.hull := D.vol_mono D.qPilot_le_hull
      _ = D.hullValue := D.hull_read
  · calc
      D.hullValue = D.vol D.hull := D.hull_read.symm
      _ <= D.vol D.thetaPilot := D.vol_mono D.hull_le_thetaPilot
      _ = D.theta := D.theta_read

/-- qPilot = thetaPilot is the endpoint-identification premise: it forces the
    two scalar readouts to be equal, independently of the hull inequalities. -/
theorem same_space_endpoint_readouts_equal (D : TightCriticData) :
    D.q = D.theta := by
  calc
    D.q = D.vol D.qPilot := D.q_read.symm
    _ = D.vol D.thetaPilot := by rw [D.qPilot_eq_thetaPilot]
    _ = D.theta := D.theta_read

/-- The tight-hull route also collapses the endpoints in the ordered space. -/
theorem same_space_tight_endpoints (D : TightCriticData) :
    D.qPilot = D.hull /\ D.hull = D.thetaPilot := by
  have h_hull_le_q : D.hull <= D.qPilot := by
    calc
      D.hull <= D.thetaPilot := D.hull_le_thetaPilot
      _ = D.qPilot := D.qPilot_eq_thetaPilot.symm
  have h_q_le_hull : D.qPilot <= D.hull := D.qPilot_le_hull
  have h_qh : D.qPilot = D.hull := le_antisymm h_q_le_hull h_hull_le_q
  refine ⟨h_qh, ?_⟩
  calc
    D.hull = D.qPilot := h_qh.symm
    _ = D.thetaPilot := D.qPilot_eq_thetaPilot

/-- The critic's contradiction needs the scalar normalization in addition to
    the endpoint identification (and, in the criticism model, the tight hull).
    The factor/negative-q assumptions make q = theta impossible. -/
theorem tight_critic_collapse (D : TightCriticData) : False := by
  have hqt : D.q = D.theta := same_space_endpoint_readouts_equal D
  exact (link_not_isometric D.q D.theta D.factor D.q_negative
    D.factor_gt_one D.theta_eq_factor_q) hqt

/-- Reuse of the source audit's same-space inequality: once thetaPilot and
    qPilot are identified and thetaPilot lies below the hull, the q-to-hull
    inequality is just monotonicity. -/
theorem same_space_q_le_hull (D : SameSpaceData) :
    D.vol D.qPilot <= D.vol D.hull :=
  same_space_inequality_is_vacuous D

/-! ## A slack/non-tight model -/

structure SlackPilotData where
  Omega : Type
  [ord : PartialOrder Omega]
  vol : Omega -> Real
  vol_mono : Monotone vol
  qPilot : Omega
  thetaPilot : Omega
  hull : Omega
  q : Real
  theta : Real
  hullValue : Real
  q_read : vol qPilot = q
  theta_read : vol thetaPilot = theta
  hull_read : vol hull = hullValue
  qPilot_le_hull : qPilot <= hull
  q_le_hullValue : q <= hullValue
  q_negative : q < 0
  factor : Real
  factor_gt_one : 1 < factor
  theta_eq_factor_q : theta = factor * q
  not_hullValue_le_theta : Not (hullValue <= theta)
  qPilot_ne_thetaPilot : Not (qPilot = thetaPilot)

attribute [instance] SlackPilotData.ord

/-- Concrete witness: same ambient ordered space and the Gaussian scalar law,
    but the hull has positive slack above theta and the endpoint identification
    is absent. -/
def slackWitness : SlackPilotData where
  Omega := Real
  ord := inferInstance
  vol := id
  vol_mono := monotone_id
  qPilot := -1
  thetaPilot := -2
  hull := -1
  q := -1
  theta := -2
  hullValue := -1
  q_read := by rfl
  theta_read := by rfl
  hull_read := by rfl
  qPilot_le_hull := by norm_num
  q_le_hullValue := by norm_num
  q_negative := by norm_num
  factor := 2
  factor_gt_one := by norm_num
  theta_eq_factor_q := by norm_num
  not_hullValue_le_theta := by norm_num
  qPilot_ne_thetaPilot := by norm_num

theorem slack_witness_properties :
    slackWitness.q < 0 /\
      1 < slackWitness.factor /\
      slackWitness.theta = slackWitness.factor * slackWitness.q /\
      slackWitness.q <= slackWitness.hullValue /\
      Not (slackWitness.hullValue <= slackWitness.theta) := by
  exact ⟨slackWitness.q_negative, slackWitness.factor_gt_one,
    slackWitness.theta_eq_factor_q, slackWitness.q_le_hullValue,
    slackWitness.not_hullValue_le_theta⟩

/-- The witness explicitly breaks the two extra critic identifications. -/
theorem slack_witness_breaks_extra_identifications :
    Not (slackWitness.qPilot = slackWitness.thetaPilot) /\
      Not (slackWitness.hullValue <= slackWitness.theta) :=
  ⟨slackWitness.qPilot_ne_thetaPilot, slackWitness.not_hullValue_le_theta⟩

/-- Formal separation statement: the scalar normalization and q <= hull can
    coexist with a non-tight hull, so tight-collapse is not a theorem of the
    weakened model. -/
theorem simplified_conflict_ne_general_slack_model :
    Exists (fun S : SlackPilotData =>
      S.q < 0 /\
      1 < S.factor /\
      S.theta = S.factor * S.q /\
      S.q <= S.hullValue /\
      Not (S.hullValue <= S.theta)) := by
  exact ⟨slackWitness, slack_witness_properties⟩

/-! ## Labeled copies and set-valued rays -/

/-- Two copies may carry the same underlying Real carrier while remaining
    distinct by label. A copy's concrete readout is additional data. -/
structure LabeledRCopy where
  label : String
  readout : Real -> Real

/-- The abstract pilot isomorphism remembers only the carrier equivalence.
    It does not include a readout-compatibility law. -/
structure AbstractPilotIso (source target : LabeledRCopy) where
  map : Real ≃ Real

def qCopy : LabeledRCopy where
  label := "q"
  readout := id

def thetaCopy : LabeledRCopy where
  label := "theta"
  readout := fun x => 2 * x

def qThetaIso : AbstractPilotIso qCopy thetaCopy where
  map := Equiv.refl Real

def ConcreteReadoutCompatible
    (source target : LabeledRCopy)
    (I : AbstractPilotIso source target) : Prop :=
  forall x : Real, source.readout x = target.readout (I.map x)

/-- The abstract isomorphism exists, but its concrete readouts need not agree. -/
theorem abstract_iso_does_not_force_readout_equality :
    Not (qCopy.readout (-1) = thetaCopy.readout (qThetaIso.map (-1))) := by
  norm_num [qCopy, thetaCopy, qThetaIso]

/-- Readout compatibility is not silently inferred from the abstract isomorphism. -/
theorem labeled_copy_readout_compatibility_is_extra :
    Not (ConcreteReadoutCompatible qCopy thetaCopy qThetaIso) := by
  intro h
  exact abstract_iso_does_not_force_readout_equality (h (-1))

/-- The Theta indeterminacy is a set-valued ray, not a selected point. -/
def thetaRay (h eps : Real) : Set Real :=
  fun x => x <= -2 * h + eps

/-- Exact membership criterion for the q-value q = -h. -/
theorem neg_h_mem_thetaRay_iff (h eps : Real) :
    Iff (thetaRay h eps (-h)) (h <= eps) := by
  change Iff (-h <= -2 * h + eps) (h <= eps)
  constructor <;> intro hh <;> linarith

/-- Membership is available only after the explicit bound h <= eps. -/
theorem neg_h_mem_thetaRay_of_bound {h eps : Real}
    (hbound : h <= eps) :
    thetaRay h eps (-h) :=
  (neg_h_mem_thetaRay_iff h eps).2 hbound

/-- Without a membership/bound premise, the ray membership statement is false
    in general; this avoids an unconditional source assignment. -/
theorem no_unconditional_neg_h_mem_thetaRay :
    Not (forall h eps : Real, thetaRay h eps (-h)) := by
  intro hmem
  have hbad : (1 : Real) <= 0 :=
    (neg_h_mem_thetaRay_iff 1 0).1 (hmem 1 0)
  norm_num at hbad

/-! ## Minimality of the endpoint-readout route -/

/-- The endpoint route uses one common carrier and one common readout.
    It requires no order, monotonicity, hull, or sign premise to force q = 0. -/
structure EndpointRouteData where
  Omega : Type
  readout : Omega -> Real
  qPilot : Omega
  thetaPilot : Omega
  qPilot_eq_thetaPilot : qPilot = thetaPilot
  q : Real
  theta : Real
  q_read : readout qPilot = q
  theta_read : readout thetaPilot = theta
  factor : Real
  factor_ne_one : factor ≠ 1
  theta_eq_factor_q : theta = factor * q

theorem endpoint_route_forces_q_zero (D : EndpointRouteData) : D.q = 0 := by
  have hqt : D.q = D.theta := by
    calc
      D.q = D.readout D.qPilot := D.q_read.symm
      _ = D.readout D.thetaPilot := by rw [D.qPilot_eq_thetaPilot]
      _ = D.theta := D.theta_read
  rw [D.theta_eq_factor_q] at hqt
  have hcoef : D.factor - 1 ≠ 0 := sub_ne_zero.mpr D.factor_ne_one
  have hmul : (D.factor - 1) * D.q = 0 := by nlinarith [hqt]
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact (hcoef hzero).elim
  · exact hzero

theorem endpoint_route_negative_impossible (D : EndpointRouteData)
    (hq : D.q < 0) : False := by
  rw [endpoint_route_forces_q_zero D] at hq
  exact (lt_irrefl 0) hq

/-- The endpoint route still has a consistent zero-readout case without the
    strict negativity premise. This shows q < 0 is sufficient for contradiction,
    but not needed to force the endpoint equation q = 0. -/
def endpointZeroWitness : EndpointRouteData where
  Omega := Real
  readout := id
  qPilot := 0
  thetaPilot := 0
  qPilot_eq_thetaPilot := rfl
  q := 0
  theta := 0
  q_read := rfl
  theta_read := rfl
  factor := 2
  factor_ne_one := by norm_num
  theta_eq_factor_q := by norm_num

theorem endpoint_zero_witness_satisfies_route :
    endpointZeroWitness.q = 0 /\
      endpointZeroWitness.theta = endpointZeroWitness.factor * endpointZeroWitness.q /\
      Not (endpointZeroWitness.q < 0) := by
  exact ⟨rfl, endpointZeroWitness.theta_eq_factor_q,
    not_lt_of_ge (le_of_eq rfl)⟩

/-! ## Minimality of the scalar tight-hull route -/

/-- The scalar route has no pilot-point identification: only q, theta, factor,
    and the two hull inequalities occur in its signature. -/
structure TightHullScalarData where
  q : Real
  theta : Real
  hull : Real
  factor : Real
  q_negative : q < 0
  factor_gt_one : 1 < factor
  theta_eq_factor_q : theta = factor * q
  q_le_hull : q <= hull
  hull_le_theta : hull <= theta

theorem negative_gaussian_scaling_separates_endpoints
    (q theta factor : Real) (hq : q < 0) (hfactor : 1 < factor)
    (htheta : theta = factor * q) : theta < q := by
  rw [htheta]
  nlinarith [mul_pos (sub_pos.mpr hfactor) (neg_pos.mpr hq)]

theorem tight_hull_route_impossible (D : TightHullScalarData) : False := by
  have hstrict : D.theta < D.q :=
    negative_gaussian_scaling_separates_endpoints D.q D.theta D.factor
      D.q_negative D.factor_gt_one D.theta_eq_factor_q
  have hweak : D.q <= D.theta := le_trans D.q_le_hull D.hull_le_theta
  linarith

/-- With factor > 1, the interval [q, factor*q] is nonempty exactly when q is
    nonnegative. In the sufficient direction choose hull = q. -/
theorem exists_between_q_and_factor_q_iff_nonneg (q factor : Real)
    (hfactor : 1 < factor) :
    (Exists fun hull : Real => q <= hull /\ hull <= factor * q) <-> 0 <= q := by
  constructor
  · rintro ⟨hull, hqHull, hHullTheta⟩
    have hqFactor : q <= factor * q := le_trans hqHull hHullTheta
    by_contra hq
    have hqneg : q < 0 := lt_of_not_ge hq
    have hprod : 0 < (factor - 1) * (-q) :=
      mul_pos (sub_pos.mpr hfactor) (neg_pos.mpr hqneg)
    nlinarith
  · intro hq
    refine ⟨q, le_rfl, ?_⟩
    nlinarith

/-- A concrete witness after dropping only the tight upper hull bound. It keeps
    q < 0, factor > 1, theta = factor*q, and q <= hull, but has theta < hull.
    Its pilot points are distinct, though the scalar-route theorem does not
    mention pilot points at all. -/
theorem drop_tight_upper_bound_witness :
    slackWitness.q < 0 /\
      1 < slackWitness.factor /\
      slackWitness.theta = slackWitness.factor * slackWitness.q /\
      slackWitness.q <= slackWitness.hullValue /\
      slackWitness.theta < slackWitness.hullValue /\
      Not (slackWitness.qPilot = slackWitness.thetaPilot) := by
  exact ⟨slackWitness.q_negative, slackWitness.factor_gt_one,
    slackWitness.theta_eq_factor_q, slackWitness.q_le_hullValue,
    by norm_num [slackWitness], slackWitness.qPilot_ne_thetaPilot⟩

/-- Concrete endpoint witness after dropping qPilot/readout compatibility:
    one abstract equivalence can carry q = -1 and theta = -2 as distinct
    concrete readouts. -/
theorem drop_endpoint_compatibility_witness :
    qCopy.readout (-1) = (-1 : Real) /\
      thetaCopy.readout (qThetaIso.map (-1)) = (-2 : Real) /\
      Not (qCopy.readout (-1) = thetaCopy.readout (qThetaIso.map (-1))) := by
  norm_num [qCopy, thetaCopy, qThetaIso]

/-- Removing the lower tight-hull bound can also be witnessed at the endpoint
    H = theta: the scalar law and the upper bound remain, while q <= H fails. -/
theorem drop_tight_lower_bound_witness :
    let q : Real := -1
    let theta : Real := -2
    let hull : Real := -2
    let factor : Real := 2
    q < 0 /\
      1 < factor /\
      theta = factor * q /\
      hull <= theta /\
      Not (q <= hull) := by
  norm_num

/-! ## Assumption-by-assumption endpoint checks

The two routes are separate sufficient contradiction mechanisms. The following
statements concern the explicitly defined toy models only. No source-theoretic
IUT compatibility or arithmetic existence statement is inferred here.
-/

/-- Algebraic endpoint core: no order, sign or hull hypotheses occur. -/
theorem endpoint_scalar_law_forces_zero (q theta factor : Real)
    (hread : q = theta) (hscale : theta = factor * q)
    (hfactor : factor ≠ 1) : q = 0 := by
  have hmul : (factor - 1) * q = 0 := by nlinarith [hread, hscale]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hfactor)

/-- A single readout of an identified abstract point suffices. -/
theorem endpoint_route_minimal {Omega : Type*} (readout : Omega → Real)
    (qPilot thetaPilot : Omega) (q theta factor : Real)
    (hpoint : qPilot = thetaPilot)
    (hq : readout qPilot = q) (htheta : readout thetaPilot = theta)
    (hscale : theta = factor * q) (hfactor : factor ≠ 1) : q = 0 := by
  apply endpoint_scalar_law_forces_zero q theta factor _ hscale hfactor
  calc
    q = readout qPilot := hq.symm
    _ = readout thetaPilot := congrArg readout hpoint
    _ = theta := htheta

/-- Nonzero q suffices for the endpoint contradiction; its sign is irrelevant. -/
theorem endpoint_route_nonzero_impossible (D : EndpointRouteData)
    (hq : D.q ≠ 0) : False :=
  hq (endpoint_route_forces_q_zero D)

theorem endpoint_route_positive_impossible (D : EndpointRouteData)
    (hq : 0 < D.q) : False :=
  endpoint_route_nonzero_impossible D (ne_of_gt hq)

/-- Negativity implies nonzero, while positive q is another nonzero case. -/
theorem negativity_is_sufficient_but_stronger_than_nonzero :
    (∀ q : Real, q < 0 → q ≠ 0) ∧
      (∃ q : Real, q ≠ 0 ∧ ¬ q < 0) := by
  exact ⟨fun _ hq => ne_of_lt hq, ⟨1, by norm_num, by norm_num⟩⟩

/-- Delete point equality, retaining one common readout and every scalar
    hypothesis of the nonzero endpoint contradiction. -/
theorem endpoint_drop_point_equality_witness :
    ∃ (readout : Real → Real) (qPilot thetaPilot q theta factor : Real),
      readout qPilot = q ∧ readout thetaPilot = theta ∧
      theta = factor * q ∧ factor ≠ 1 ∧ q ≠ 0 ∧ qPilot ≠ thetaPilot := by
  refine ⟨id, -1, -2, -1, -2, 2, ?_⟩
  norm_num

/-- Delete common-readout compatibility while keeping the same abstract point.
    This is also the concrete readout pair of the identity abstract Equiv. -/
theorem endpoint_drop_common_readout_witness :
    ∃ (qReadout thetaReadout : Real → Real) (pilot q theta factor : Real),
      qReadout pilot = q ∧ thetaReadout pilot = theta ∧
      theta = factor * q ∧ factor ≠ 1 ∧ q ≠ 0 ∧ q ≠ theta := by
  refine ⟨id, (fun x => 2 * x), -1, -1, -2, 2, ?_⟩
  norm_num

/-- Delete factor ≠ 1: equal negative endpoints and the scalar law coexist. -/
theorem endpoint_drop_factor_ne_one_witness :
    ∃ q theta factor : Real,
      q = theta ∧ theta = factor * q ∧ q < 0 ∧ factor = 1 := by
  refine ⟨-1, -1, 1, ?_⟩
  norm_num

/-- Delete the scalar law: equal negative endpoints coexist with factor ≠ 1. -/
theorem endpoint_drop_scalar_law_witness :
    ∃ q theta factor : Real,
      q = theta ∧ factor ≠ 1 ∧ q < 0 ∧ theta ≠ factor * q := by
  refine ⟨-1, -1, 2, ?_⟩
  norm_num

/-! ## Assumption-by-assumption tight-interval checks -/

/-- Scalar tight interval contradiction: point equality is absent. -/
theorem tight_interval_route_minimal (q theta hull factor : Real)
    (hq : q < 0) (hfactor : 1 < factor) (hscale : theta = factor * q)
    (hlower : q ≤ hull) (hupper : hull ≤ theta) : False := by
  have hstrict := negative_gaussian_scaling_separates_endpoints
    q theta factor hq hfactor hscale
  exact (not_le_of_gt hstrict) (hlower.trans hupper)

/-- Deleting the upper bound permits the endpoint hull = q. -/
theorem delete_upper_bound_take_q (q theta : Real) (hstrict : theta < q) :
    ∃ hull : Real, q ≤ hull ∧ ¬ hull ≤ theta :=
  ⟨q, le_rfl, not_le_of_gt hstrict⟩

/-- Deleting the lower bound permits the endpoint hull = theta. -/
theorem delete_lower_bound_take_theta (q theta : Real) (hstrict : theta < q) :
    ∃ hull : Real, hull ≤ theta ∧ ¬ q ≤ hull :=
  ⟨theta, le_rfl, not_le_of_gt hstrict⟩

/-- Delete negative q: positive q satisfies both bounds and factor > 1. -/
theorem tight_drop_negative_q_witness :
    ∃ q theta hull factor : Real,
      0 < q ∧ 1 < factor ∧ theta = factor * q ∧ q ≤ hull ∧ hull ≤ theta := by
  refine ⟨1, 2, 1, 2, ?_⟩
  norm_num

/-- Delete factor > 1, even retaining factor ≠ 1: a factor below one permits
    a tight interval for negative q. -/
theorem tight_drop_factor_gt_one_witness :
    ∃ q theta hull factor : Real,
      q < 0 ∧ factor ≠ 1 ∧ ¬ 1 < factor ∧ theta = factor * q ∧
      q ≤ hull ∧ hull ≤ theta := by
  refine ⟨-1, -(1 / 2), -1, 1 / 2, ?_⟩
  norm_num

/-- Delete the scalar law: negative equal endpoints permit both tight bounds. -/
theorem tight_drop_scalar_law_witness :
    ∃ q theta hull factor : Real,
      q < 0 ∧ 1 < factor ∧ q ≤ hull ∧ hull ≤ theta ∧ theta ≠ factor * q := by
  refine ⟨-1, -1, -1, 2, ?_⟩
  norm_num

end LeanFormal.IUTDisputeSimplification
