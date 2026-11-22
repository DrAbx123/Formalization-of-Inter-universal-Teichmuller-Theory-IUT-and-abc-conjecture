import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import LeanFormal.IUT.Audit.Status

/-!
# Card-AMPL: the interface-level hull log-volume upper bound as a named supply

This module solidifies the Card-AMPL card of the Step-XI contract reduction
(`logs/coordination/stepxi-contract-reduction-20261016.md`, section 3) at the same
depth as the Card-IPL transport-laws module
(`LeanFormal/IUT/IUTIII/Theorem311/SourcePolyIsoTransportLaws.lean`): the conditional
assembly path of the upper side of the Corollary 3.12 hull bound is re-housed as a
consumable `LeanFormal` module.

## Original (paper) route

* IUT III, Corollary 3.12, proof: compactness of the `1,◦U_{j,vQ}` together with the
  definition of the log-volume (and the hull containment of Remark 3.9.5, (ii)) give
  that the holomorphic hull of the theta-pilot object has finite log-volume, bounded
  above by the ambient Theta-data; the Corollary 3.12 conclusion `q <= Theta` combines
  this upper side with the lower side coming from the image union.
* IUT III, Remark 3.9.5: the normalization of the log-volume on the unit region and
  the `lambda·O`-compatibility are the ambient data consumed by the interface
  `IQHullLogVolumeInterface`.

## Reduced route (unchanged from the reuse files)

R1. The hull carrier is the data interface `IQHullLogVolumeInterface`
    (`SourceHullCompactnessReduction.lean`); no claim is made that the actual
    `IQ(S±_{j+1}; n,◦D^vdash_{vQ})` carrier realizes it -- that is Card-HULLREAL, a
    different owner.
R2. The upper bound itself is supplied, never derived: at the value level it is
    unsatisfiable under pointwise degree faithfulness
    (`sourceThetaBound_unsat_of_degreeFaithful`), relied on as recorded history and
    NOT re-proved here.
R3. Only the conditional assembly path is frozen: named supply fields (the fields are
    discharge obligations), reduction laws between the interface-level `ENNReal`
    bound and the real field consumed by `CertificateHullWiring`, and the consumer
    alignment with `iqHullCertificate`.

## What is frozen here

* `CardAMPLThetaBoundSupply` -- the named supply: a real `theta` with `0 <= theta`
  and the interface-level upper bound `W.logVolume W.hull <= ofReal theta`; no source
  instantiation is constructed or asserted;
* reduction laws: `realVolume_le` (the supply feeds the consumer's real field through
  the proved equivalence `iqHullRealVolume_le_theta_iff`),
  `ofReal_le_theta_of_imageSet_lower` (lower-to-upper transfer through the hull),
  `exists_hull_eq_ofReal` (exact reconstruction shape), `of_realVolume_le` (converse
  constructor from a real bound), and `nonempty_iff` (the exact quantifier form);
* consumer alignment: `certificate`, `linkEvidence`, and `cor312Conclusion` replace
  the `q`/`theta`/`hθ`/`hθ0` argument packages of `CertificateHullWiring` by the
  named supply, and `certificate_thetaSigned` records `thetaSigned = S.theta`;
* non-vacuity: `singletonRealSupply` instantiates the supply on the one-point witness
  `singletonRealWitness` (with `theta = 1`), showing that the supply is satisfiable.

Candidate status: conditional on the supply fields; nothing about the actual source
carrier is claimed, and the degree-faithful boundary is left as recorded.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

universe u v

/-- **Card-AMPL named supply.**  The upper-bound side of the Corollary 3.12 hull
log-volume bound, as interface-level data over `IQHullLogVolumeInterface`: a real
upper-bound constant `theta` with `0 <= theta`, and the bound
`W.logVolume W.hull <= ENNReal.ofReal theta`.

The fields are discharge obligations, not consequences of the interface: (O1)
`theta` -- the role of the ambient Theta-constant (its identification for the actual
carrier is not constructed here); (O2) `theta_nonneg` -- the sign normalization; (O3)
`hull_logVolume_le` -- the Card-AMPL upper bound itself.  The consumer slot is
`StepXIFiniteCertificate.hull_le_theta` of `CertificateHullWiring`. -/
structure CardAMPLThetaBoundSupply {X : Type u} (W : IQHullLogVolumeInterface X) where
  /-- (O1) The upper-bound constant (the role of the Theta-data of Corollary 3.12). -/
  theta : ℝ
  /-- (O2) The sign normalization of the constant. -/
  theta_nonneg : 0 ≤ theta
  /-- (O3) The upper bound: the hull log-volume is at most `ofReal theta`. -/
  hull_logVolume_le : W.logVolume W.hull ≤ ENNReal.ofReal theta

namespace CardAMPLThetaBoundSupply

variable {X : Type u} {W : IQHullLogVolumeInterface X}

/-- **Reduction law (real form).**  The supply's interface-level bound feeds the real
field consumed by `CertificateHullWiring`, through the proved equivalence
`iqHullRealVolume_le_theta_iff`; this is exactly the `hull_le_theta` slot of
`iqHullCertificate`. -/
theorem realVolume_le (S : CardAMPLThetaBoundSupply W) :
    iqHullRealVolume W ≤ S.theta :=
  (iqHullRealVolume_le_theta_iff W (θ := S.theta) S.theta_nonneg).mpr S.hull_logVolume_le

/-- **Reduction law (lower-to-upper transfer).**  Any `ofReal q` lower bound obtained
on the image union (the lower side of the consumer package) transfers through the
hull to the supply's constant. -/
theorem ofReal_le_theta_of_imageSet_lower (S : CardAMPLThetaBoundSupply W)
    {q : ℝ} (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet) :
    q ≤ S.theta :=
  (ENNReal.ofReal_le_ofReal_iff S.theta_nonneg).mp
    (le_trans hq (le_trans W.imageSet_logVolume_le_hull S.hull_logVolume_le))

/-- **Exact reconstruction shape.**  The hull log-volume is exactly the `ofReal` of a
real number bounded by the supply's constant. -/
theorem exists_hull_eq_ofReal (S : CardAMPLThetaBoundSupply W) :
    ∃ M : ℝ, W.logVolume W.hull = ENNReal.ofReal M ∧ M ≤ S.theta :=
  ⟨iqHullRealVolume W, iqHull_logVolume_hull_eq_ofReal W, S.realVolume_le⟩

/-- **Converse constructor.**  A real upper bound on `iqHullRealVolume` together with
the sign condition constructs a supply: the real field of the consumer and the named
supply carry the same content. -/
def of_realVolume_le {θ : ℝ} (hθ0 : 0 ≤ θ) (h : iqHullRealVolume W ≤ θ) :
    CardAMPLThetaBoundSupply W where
  theta := θ
  theta_nonneg := hθ0
  hull_logVolume_le := (iqHullRealVolume_le_theta_iff W (θ := θ) hθ0).mp h

/-- **Exactness.**  A supply exists exactly when some `theta >= 0` bounds the hull
log-volume at the interface level; the existential quantifier is the only freedom,
the remaining fields being forced. -/
theorem nonempty_iff :
    Nonempty (CardAMPLThetaBoundSupply W) ↔
      ∃ θ : ℝ, 0 ≤ θ ∧ W.logVolume W.hull ≤ ENNReal.ofReal θ :=
  ⟨fun ⟨S⟩ => ⟨S.theta, S.theta_nonneg, S.hull_logVolume_le⟩,
    fun ⟨θ, hθ0, hθ⟩ =>
      ⟨{ theta := θ, theta_nonneg := hθ0, hull_logVolume_le := hθ }⟩⟩

/-- **Non-vacuity.**  The one-point witness `singletonRealWitness` (with `hull = {0}`
and `logVolume {0} = 1`) carries a supply with `theta = 1`.  This is a consistency
check on the supply only, not a model of the paper's carrier. -/
noncomputable def singletonRealSupply :
    CardAMPLThetaBoundSupply (IQHullLogVolumeInterface.singletonRealWitness) where
  theta := 1
  theta_nonneg := zero_le_one
  hull_logVolume_le := by
    classical
    have hne : ({0} : Set ℝ).Nonempty := ⟨0, rfl⟩
    simp [IQHullLogVolumeInterface.singletonRealWitness, hne, ENNReal.ofReal_one]

/-! ## Consumer alignment (the `CertificateHullWiring` package, re-indexed) -/

/-- The full `StepXIFiniteCertificate` package of `iqHullCertificate`, with the
`theta`/`hθ`/`hθ0` arguments replaced by the named supply; the remaining arguments
are the same as in `CertificateHullWiring`. -/
def certificate (S : CardAMPLThetaBoundSupply W)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (q : ℝ) (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet) (hqneg : q < 0) :
    StepXIFiniteCertificate label :=
  iqHullCertificate W pt hpt data hvalue hw q S.theta hq S.hull_logVolume_le
    S.theta_nonneg hqneg

/-- The certificate's `thetaSigned` is the supply constant: the Card-AMPL datum
occupies exactly the consumer's upper-bound slot. -/
@[simp] theorem certificate_thetaSigned (S : CardAMPLThetaBoundSupply W)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (q : ℝ) (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet) (hqneg : q < 0) :
    (S.certificate pt hpt data hvalue hw q hq hqneg).thetaSigned = S.theta := rfl

/-- The link evidence of `FiniteCertificateBridge` for the supply certificate, with
`targetSigned := iqHullRealVolume`; the IPL/SHE/APT propositions and their evidence
are supplied externally, exactly as in `iqHullLinkEvidence`. -/
def linkEvidence (S : CardAMPLThetaBoundSupply W)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (q : ℝ) (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet) (hqneg : q < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence (S.certificate pt hpt data hvalue hw q hq hqneg) where
  targetSigned := iqHullRealVolume W
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := (S.certificate pt hpt data hvalue hw q hq hqneg).q_le_hull
  target_le_theta := (S.certificate pt hpt data hvalue hw q hq hqneg).hull_le_theta

/-- **Headline composition.**  From the named supply and the same remaining inputs as
`iqHullCor312Conclusion`, the existing bridge assembly yields the Corollary 3.12
contract conclusion. -/
theorem cor312Conclusion (S : CardAMPLThetaBoundSupply W)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (q : ℝ) (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet) (hqneg : q < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((S.certificate pt hpt data hvalue hw q hq hqneg).toContract
        (S.linkEvidence pt hpt data hvalue hw q hq hqneg ipl she apt hipl hshe hapt)) :=
  cor312_of_finite_certificate _ _

end CardAMPLThetaBoundSupply

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the Card-AMPL conditional supply: the interface-level upper
bound of the Corollary 3.12 hull log-volume as named supply data, its reduction laws,
and its alignment with the `CertificateHullWiring` consumer. -/
def cardAMPLThetaBoundSupply : Obligation :=
  { id := "IUT-III.card-ampl-theta-bound-supply"
    source :=
      "IUT III, Corollary 3.12, proof (compactness of the 1,circ U_{j,vQ} and the " ++
        "definition of the log-volume; upper bound q <= Theta); Remark 3.9.5"
    status := VerificationStatus.interface
    note :=
      "Solidified the Card-AMPL conditional assembly path over the reuse surface " ++
        "CertificateHullWiring.lean (SHA256 " ++
        "FEF2CA985A7010A77B768426FF661DFA3021B621980B14D5202674110C95191A): the " ++
        "named supply CardAMPLThetaBoundSupply (theta; 0 <= theta; logVolume hull " ++
        "<= ofReal theta; fields are discharge obligations, no source " ++
        "instantiation constructed); reduction laws realVolume_le (through the " ++
        "proved equivalence iqHullRealVolume_le_theta_iff), " ++
        "ofReal_le_theta_of_imageSet_lower, exists_hull_eq_ofReal, of_realVolume_le " ++
        "(converse constructor), nonempty_iff (exact quantifier form); consumer " ++
        "alignment certificate / linkEvidence / cor312Conclusion re-index " ++
        "iqHullCertificate / iqHullLinkEvidence / iqHullCor312Conclusion by the " ++
        "supply, with certificate_thetaSigned recording thetaSigned = S.theta; " ++
        "non-vacuity singletonRealSupply on the one-point witness. Boundary " ++
        "retained, not re-proved: under pointwise degree faithfulness the " ++
        "value-level upper bound is unsatisfiable " ++
        "(sourceThetaBound_unsat_of_degreeFaithful). NOT proved: a realization of " ++
        "the interface and of the theta bound for the actual source carrier " ++
        "(Card-HULLREAL, different owner)."
    dependsOn :=
      [ "IUT-III.corollary-3.12-step-XI-certificate-hull-wiring",
        "IUT-III.corollary-3.12-iq-hull-log-volume-interface" ] }

end LeanFormal.IUT.Audit
