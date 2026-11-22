import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# H4: hull <= theta — complete-proof consumer of the Card-AMPL certificate supply

H4 (hull <= theta) is the upper-side log-volume bound of the Corollary 3.12 hull
candidate.  The production Card-AMPL module already freezes the named supply and
its reduction laws with COMPLETE proofs:
LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardAMPLThetaBoundSupply.lean
(CardAMPLThetaBoundSupply: gamma; realVolume_le; ofReal_le_theta_of_imageSet_lower;
exists_hull_eq_ofReal; of_realVolume_le; nonempty_iff; certificate; cor312Conclusion).
This file is the H4 consumer layer: it re-exposes those complete proofs in the H4
shape and records the exact remaining GAP honestly (the supply fields must be
discharged for the actual source carrier).

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.H4HullThetaCertificateActual

open LeanFormal.IUT

universe u v

variable {X : Type u} {W : IQHullLogVolumeInterface X}

/-- H4 real form: the hull real log-volume is bounded by the supply constant. -/
theorem h4_iqHullRealVolume_le (S : CardAMPLThetaBoundSupply W) :
    iqHullRealVolume W ≤ S.theta :=
  S.realVolume_le

/-- H4 ENNReal form: the hull log-volume is at most ofReal theta. -/
theorem h4_hull_logVolume_le (S : CardAMPLThetaBoundSupply W) :
    W.logVolume W.hull ≤ ENNReal.ofReal S.theta :=
  S.hull_logVolume_le

/-- H4 exact reconstruction: the hull log-volume is ofReal of a real number bounded
by the supply constant. -/
theorem h4_exists_hull_eq_ofReal (S : CardAMPLThetaBoundSupply W) :
    ∃ M : ℝ, W.logVolume W.hull = ENNReal.ofReal M ∧ M ≤ S.theta :=
  S.exists_hull_eq_ofReal

/-- H4 lower-to-upper transfer through the hull (image-union lower bound). -/
theorem h4_ofReal_le_theta_of_imageSet_lower (S : CardAMPLThetaBoundSupply W)
    {q : ℝ} (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet) :
    q ≤ S.theta :=
  S.ofReal_le_theta_of_imageSet_lower hq

/-- H4 non-vacuity shape: a supply exists iff there is a nonnegative ofReal upper
bound of the hull log-volume. -/
theorem h4_nonempty_iff :
    Nonempty (CardAMPLThetaBoundSupply W) ↔
      ∃ θ : ℝ, 0 ≤ θ ∧ W.logVolume W.hull ≤ ENNReal.ofReal θ :=
  CardAMPLThetaBoundSupply.nonempty_iff

/-- H4 certificate consumer: the Card-AMPL certificate yields the Corollary 3.12
conclusion (complete proof, reused), conditional on the supplied q/image-set data. -/
theorem h4_cor312Conclusion (S : CardAMPLThetaBoundSupply W)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (q : ℝ) (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet) (hqneg : q < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((S.certificate pt hpt data hvalue hw q hq hqneg).toContract
        (S.linkEvidence pt hpt data hvalue hw q hq hqneg ipl she apt
          hipl hshe hapt)) :=
  S.cor312Conclusion pt hpt data hvalue hw q hq hqneg ipl she apt hipl hshe hapt

/-- H4 status record: (component, evidence, status). -/
def h4Status : List (String × String × String) :=
  [ ("H4 hull <= theta (real form)", "h4_iqHullRealVolume_le (from CardAMPLThetaBoundSupply.realVolume_le)", "COMPLETE PROOF (consumer; conditional on supply fields)"),
    ("H4 hull <= theta (ENNReal form)", "h4_hull_logVolume_le", "COMPLETE PROOF (consumer)"),
    ("H4 exact reconstruction", "h4_exists_hull_eq_ofReal", "COMPLETE PROOF (consumer)"),
    ("H4 image-union transfer", "h4_ofReal_le_theta_of_imageSet_lower", "COMPLETE PROOF (consumer)"),
    ("H4 Cor 3.12 certificate conclusion", "h4_cor312Conclusion", "COMPLETE PROOF (consumer)"),
    ("H4 remaining GAP", "supply fields theta/theta_nonneg/hull_logVolume_le for the ACTUAL source carrier", "GAP: not constructed; class-B source instantiation (Card-HULLREAL/AMPL boundary)") ]

end LeanFormal.IUT.XiFPaper.H4HullThetaCertificateActual

end
