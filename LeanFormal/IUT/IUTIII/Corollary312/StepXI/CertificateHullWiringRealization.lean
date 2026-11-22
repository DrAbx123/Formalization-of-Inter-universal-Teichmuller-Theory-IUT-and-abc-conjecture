import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierConcreteModel

/-!
# Filling the CertificateHullWiring d5 slots at the concrete carrier model (N14)

`CertificateHullWiring.lean` wires any realization `W : IQHullLogVolumeInterface X`
into the Step-XI finite certificate consumers, but left the following slots as
supplied hypotheses (formerly "waiting for the d5 carrier"):

* the realization `W` itself;
* the two interface-level bounds `ofReal q <= W.logVolume W.imageSet` and
  `W.logVolume W.hull <= ofReal theta`, together with `0 <= theta` and `q < 0`.

This module fills all of those slots at the concrete real-line carrier
`iqCarrierModelInterface` of `IQCarrierConcreteModel.lean` (task d5), with the
explicit values `q = -1` and `theta = 0` (the model hull and image-set
log-volumes both compute to `0`), a one-point finite labeling, and explicit
`WeightedValues` bookkeeping.  Everything below is proved; the remaining
inputs are the source-facing IPL/SHE/APT evidence (not hull-related, kept
explicit, never closed by trivial instantiations here) and the comparison
leg's named arithmetic inputs (`0 <= eps` and the H1 valuation bound).

## Relation to the N9 chain route

The certificate terminal `Cor312Conclusion` and the adopted reduced-form
comparison terminal `Cor312EpsilonArithmeticComparison` are type-level separate
consumers; the defs of `IQCarrierRealizationAlignment.lean` are value-carrier
facing and no slot of the certificate wiring can consume them.  The comparison
leg at the d5 carrier is `iqCarrierModel_epsilonComparison` (d5 file, the model
side of the approved reduced form), and `iqCarrierModelWiring_twoLegs` below
records the two legs at one carrier.  At the value-realized carrier the same
wiring remains carded: the realization slot requires the actual carrier data
(Card-HULLREAL), the upper bound `logVolume hull <= ofReal theta` is
unsatisfiable under pointwise degree faithfulness
(`sourceThetaBound_unsat_of_degreeFaithful`, CertificateHullWiring), and the
`q < 0` slot is the packet contraction condition (`sourceThetaValue_neg_iff`) -
recorded, not supplied, here.
-/

namespace LeanFormal.IUT

noncomputable section

/-! ## 1. Computed model values: hull and image-set log-volumes -/

/-- The real hull volume of the d5 model carrier is `0`. -/
theorem iqCarrierModelRealVolume_eq_zero :
    iqHullRealVolume iqCarrierModelInterface = 0 := by
  change (realLineLogVolume (Set.Iic (0 : Real))).toReal = 0
  rw [iqCarrierModelLogVolume_Iic_zero]
  simp

/-- Interface-level lower bound slot: `ofReal (-1) <= logVolume imageSet`. -/
theorem iqCarrierModelWiring_hq :
    ENNReal.ofReal (-1 : Real) <=
      iqCarrierModelInterface.logVolume iqCarrierModelInterface.imageSet := by
  change ENNReal.ofReal (-1 : Real) <= realLineLogVolume (Set.Iic (0 : Real))
  rw [iqCarrierModelLogVolume_Iic_zero]
  exact le_of_eq (ENNReal.ofReal_of_nonpos (by norm_num : (-1 : Real) <= 0))

/-- Interface-level upper bound slot: `logVolume hull <= ofReal 0`. -/
theorem iqCarrierModelWiring_hTheta :
    iqCarrierModelInterface.logVolume iqCarrierModelInterface.hull <=
      ENNReal.ofReal (0 : Real) := by
  change realLineLogVolume (Set.Iic (0 : Real)) <= ENNReal.ofReal (0 : Real)
  rw [iqCarrierModelLogVolume_Iic_zero, ENNReal.ofReal_zero]

/-! ## 2. The one-point finite labeling and the weighted values -/

/-- The one-point finite hull at the model: the point `0` in the image log-shell. -/
def iqCarrierModelWiringFiniteHull : FiniteHull Unit :=
  iqHullFiniteHull iqCarrierModelInterface (fun _ => (0 : Real))
    (fun _ => le_refl (0 : Real))

/-- The point volume evaluates to `0` (the singleton log-volume of `0`). -/
theorem iqCarrierModelWiringFiniteHull_volume (i : Unit) :
    iqCarrierModelWiringFiniteHull.volume i = 0 := by
  change (realLineLogVolume {(0 : Real)}).toReal = 0
  rw [realLineLogVolume_singleton, ENNReal.toReal_ofReal (le_refl (0 : Real))]

/-- Weighted data matching the one-point hull: value `0`, weight `1`. -/
def iqCarrierModelWiringWeightedValues : WeightedValues Unit where
  value := fun _ => 0
  weight := fun _ => 1
  weightTotal := 1
  weightTotal_pos := one_pos
  weightTotal_eq_sum := by simp

/-- The weighted average evaluates to exactly `0`. -/
theorem iqCarrierModelWiringWeightedValues_average_eq :
    iqCarrierModelWiringWeightedValues.average = 0 := by
  refine le_antisymm ?_ ?_
  · have h := iqHullFiniteHull_average_le iqCarrierModelInterface (fun _ => (0 : Real))
      (fun _ => le_refl (0 : Real)) iqCarrierModelWiringWeightedValues
      (fun i => (iqCarrierModelWiringFiniteHull_volume i).symm)
      (fun _ => zero_le_one)
    rwa [iqCarrierModelRealVolume_eq_zero] at h
  · exact WeightedValues.lower_le_average_of_pointwise iqCarrierModelWiringWeightedValues
      (fun _ => zero_le_one) (fun _ => le_rfl)

/-! ## 3. The certificate, its link evidence, and the two carrier legs -/

/-- **The CertificateHullWiring certificate at the d5 model**, with the explicit
values `q = -1` and `theta = 0`. -/
def iqCarrierModelWiringCertificate : StepXIFiniteCertificate Unit :=
  iqHullCertificate iqCarrierModelInterface (fun _ => (0 : Real))
    (fun _ => le_refl (0 : Real)) iqCarrierModelWiringWeightedValues
    (fun i => (iqCarrierModelWiringFiniteHull_volume i).symm)
    (fun _ => zero_le_one) (-1) 0 iqCarrierModelWiring_hq iqCarrierModelWiring_hTheta
    (le_rfl : (0 : Real) <= 0) (by norm_num : (-1 : Real) < 0)

/-- The certificate's lower signed value is the computed concrete value. -/
theorem iqCarrierModelWiringCertificate_qSigned :
    iqCarrierModelWiringCertificate.qSigned = -1 := rfl

/-- The certificate's upper signed value is the computed concrete value. -/
theorem iqCarrierModelWiringCertificate_thetaSigned :
    iqCarrierModelWiringCertificate.thetaSigned = 0 := rfl

/-- The certificate hull volume is the real hull volume of the model, i.e. `0`. -/
theorem iqCarrierModelWiringCertificate_hullVolume :
    iqCarrierModelWiringCertificate.hull.hullVolume = 0 := by
  change iqHullRealVolume iqCarrierModelInterface = 0
  exact iqCarrierModelRealVolume_eq_zero

/-- The link evidence at the model; the IPL/SHE/APT evidence stays an explicit
input. -/
def iqCarrierModelWiringLinkEvidence (ipl she apt : Prop) (hipl : ipl)
    (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence iqCarrierModelWiringCertificate :=
  iqHullLinkEvidence iqCarrierModelInterface (fun _ => (0 : Real))
    (fun _ => le_refl (0 : Real)) iqCarrierModelWiringWeightedValues
    (fun i => (iqCarrierModelWiringFiniteHull_volume i).symm)
    (fun _ => zero_le_one) (-1) 0 iqCarrierModelWiring_hq iqCarrierModelWiring_hTheta
    (le_rfl : (0 : Real) <= 0) (by norm_num : (-1 : Real) < 0)
    ipl she apt hipl hshe hapt

/-- **The certificate leg at the d5 carrier**: the Corollary 3.12 contract
conclusion through the existing finite-certificate assembly. -/
theorem iqCarrierModelWiring_cor312Conclusion (ipl she apt : Prop) (hipl : ipl)
    (hshe : she) (hapt : apt) :
    Cor312Conclusion
      (iqCarrierModelWiringCertificate.toContract
        (iqCarrierModelWiringLinkEvidence ipl she apt hipl hshe hapt)) :=
  cor312_of_finite_certificate iqCarrierModelWiringCertificate
    (iqCarrierModelWiringLinkEvidence ipl she apt hipl hshe hapt)

/-- **Both d5-carrier legs in one statement**: the adopted comparison route's
model instance (`iqCarrierModel_epsilonComparison`, the model side of the
approved reduced form) and the certificate conclusion above. -/
def iqCarrierModelWiring_twoLegs {eps : Real} (heps : 0 <= eps)
    (hval : forall a b c : Nat, IsABCTriple a b c ->
      forall q, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) ->
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) <= 1 + eps)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    PProd (Cor312EpsilonArithmeticComparison iqCarrierModelInterface eps)
      (Cor312Conclusion
        (iqCarrierModelWiringCertificate.toContract
          (iqCarrierModelWiringLinkEvidence ipl she apt hipl hshe hapt))) :=
  ⟨iqCarrierModel_epsilonComparison heps hval,
    iqCarrierModelWiring_cor312Conclusion ipl she apt hipl hshe hapt⟩

/-- **Both d5-carrier legs, additive form (version-2 mirror of
`iqCarrierModelWiring_twoLegs`).**  The comparison leg is the model-side
instance of the approved additive re-freeze
(`iqCarrierModel_epsilonComparisonAdditive`, consuming the contract-v2 input
`height ≤ (1 + ε) · weight + A` instead of the refuted valuation bound); the
certificate leg is unchanged. -/
def iqCarrierModelWiring_twoLegsAdditive {eps A : Real} (heps : 0 <= eps)
    (hadd : forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c) <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    PProd (Cor312EpsilonArithmeticComparisonAdditive iqCarrierModelInterface eps A)
      (Cor312Conclusion
        (iqCarrierModelWiringCertificate.toContract
          (iqCarrierModelWiringLinkEvidence ipl she apt hipl hshe hapt))) :=
  ⟨iqCarrierModel_epsilonComparisonAdditive heps hadd,
    iqCarrierModelWiring_cor312Conclusion ipl she apt hipl hshe hapt⟩

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the d5-carrier wiring of `CertificateHullWiring` (task N14). -/
def certificateHullWiringRealization : Obligation :=
  { id := "IUT-III.corollary-3.12-step-XI-certificate-hull-wiring-realization"
    source :=
      "IUT III, Corollary 3.12, Step (xi): CertificateHullWiring d5 slots filled " ++
        "at the concrete carrier model"
    status := VerificationStatus.interface
    note :=
      "The realization W, the two interface bounds (ofReal q <= logVolume " ++
        "imageSet and logVolume hull <= ofReal theta), 0 <= theta, and q < 0 of " ++
        "CertificateHullWiring are discharged at iqCarrierModelInterface with " ++
        "explicit q = -1 and theta = 0 (hull and image-set log-volumes both 0), a " ++
        "one-point finite labeling, and explicit WeightedValues; the resulting " ++
        "certificate, link evidence (IPL/SHE/APT still supplied inputs), the " ++
        "Cor312Conclusion, and the joint certificate/comparison statement at the " ++
        "carrier are proved (the comparison leg is the model-side instance of the " ++
        "approved reduced form). Still carded at the value-realized carrier: the " ++
        "carrier realization (Card-HULLREAL), the theta upper bound " ++
        "(unsatisfiable under pointwise degree faithfulness), and the contraction " ++
        "input q < 0."
    dependsOn :=
      [ "IUT-III.corollary-3.12-step-XI-certificate-hull-wiring",
        "IUT-III.corollary-3.12-iq-carrier-concrete-model-spike" ] }

end LeanFormal.IUT.Audit
