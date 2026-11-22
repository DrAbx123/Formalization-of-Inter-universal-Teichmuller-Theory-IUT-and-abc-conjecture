import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import Mathlib.Tactic

/-!
# Certificate-side transfer of the terminal Corollary 3.12 bound (Steps (xi-d)-(xi-f))

Frozen target: the construction face of the obligation
`IUT-III.holomorphic-hull-determinant-log-volume`
(`HolomorphicHull/Volume.lean:179`).  This module does not construct the
paper's carrier or its holomorphic hull.  It wires the finite certificate
supply structure `StepXIFiniteCertificate` (`Volume.lean:152`) to the
terminal inequality of Corollary 3.12, Step (xi-f).

## Original-text anchors

Transcription: `papers/motizuki_corpus/text/source_audit/`
`IUTIII_Theorem311_pp153-159_Corollary312_pp173-186.plain.txt`.

* Step (xi-d), lines 1070-1096: the determinant (suitable positive tensor
  power) of the localizations of arithmetic vector bundles, and the
  `j in |Fl|`-normalized log-volume applied to the region `1,U` and to the
  q-pilot region; `-|log(q)| in R`; the definition
  `R_{<= -|log(Theta)|} = {lambda in R | lambda <= -|log(Theta)|}`.
* Step (xi-f), lines 1136-1146: `-|log(q)| in R_{<= -|log(Theta)|}`, hence
  `-|log(q)| <= -|log(Theta)|`, hence `C_Theta >= -1` for any `C_Theta in R`
  with `-|log(Theta)| <= C_Theta * |log(q)|`.

## Proved here (over any supplied certificate)

* `StepXIFiniteCertificate.weighted_average_le_theta`: the certificate's
  normalized `WeightedValues` average of the hull volumes lies below the
  `-|log(Theta)|` scalar.  This is the general certificate-level form of the
  concrete instance bounds `ConcreteFiniteRouteColumns.lean:1066` and
  `SourceRouteDeterminantNormalization.lean:181`.
* `cTheta_lower_bound_of_finiteCertificate`: the Step (xi-f) transfer
  `-1 <= C_Theta`, with the paper's `|log(q)| > 0` supplied by the
  certificate field `q_negative` through the explicit identification
  `|log(q)| = -qSigned`.
* `cTheta_lower_bound_of_finiteCertificate_expTwo`: a satisfiability witness
  at the one-point certificate.

## Honest boundaries

No certificate is constructed here for the actual source carrier; the
identification `|log(q)| = -qSigned` is an explicit hypothesis, not asserted;
the carrier realization (Card-HULLREAL) remains a separate source obligation
of `IUT-III.holomorphic-hull-determinant-log-volume`.
-/

namespace LeanFormal.IUT

noncomputable section

/-- The normalized average of the hull volumes lies below `-|log(Theta)|`:
the certificate's `WeightedValues` average is bounded by the hull volume,
which the certificate bounds by `thetaSigned`. -/
theorem StepXIFiniteCertificate.weighted_average_le_theta {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label) :
    certificate.weighted.average <= certificate.thetaSigned :=
  le_trans
    (certificate.hull.average_le certificate.weighted certificate.weighted_matches_hull
      certificate.weights_nonnegative)
    certificate.hull_le_theta

/-- Step (xi-f) transfer over a supplied certificate: from
`-|log(Theta)| <= C_Theta * |log(q)|` and the certificate chain
`qSigned <= hull <= thetaSigned`, conclude `-1 <= C_Theta`.

The hypothesis `hq` is the explicit identification `|log(q)| = -qSigned`;
combined with the certificate field `q_negative` it also supplies the
paper's hypothesis `|log(q)| > 0`.  `thetaSigned` is read as
`-|log(Theta)|` and `hc` is the paper's displayed condition. -/
theorem cTheta_lower_bound_of_finiteCertificate {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label) {q : Real}
    (hq : |Real.log q| = -certificate.qSigned) {cTheta : Real}
    (hc : certificate.thetaSigned <= cTheta * |Real.log q|) :
    -1 <= cTheta := by
  have hden : 0 < -certificate.qSigned := neg_pos.mpr certificate.q_negative
  have htheta : certificate.thetaSigned <= cTheta * (-certificate.qSigned) := by
    rw [hq] at hc
    exact hc
  have hchain : certificate.qSigned <= certificate.thetaSigned :=
    certificate.q_le_theta
  have hmul : -certificate.qSigned * (-1) <= -certificate.qSigned * cTheta := by
    calc
      -certificate.qSigned * (-1) = certificate.qSigned := by ring
      _ <= certificate.thetaSigned := hchain
      _ <= cTheta * (-certificate.qSigned) := htheta
      _ = -certificate.qSigned * cTheta := by ring
  exact (mul_le_mul_iff_of_pos_left hden).mp hmul

/-- Satisfiability witness: the one-point certificate with `qSigned = -2`,
`thetaSigned = -1`, the q-parameter `exp 2` (so `|log(q)| = 2 = -qSigned`),
and `C_Theta = -1/2` realizes the transfer's hypotheses. -/
theorem cTheta_lower_bound_of_finiteCertificate_expTwo :
    -1 <= (-1 / 2 : Real) := by
  let hcert : StepXIFiniteCertificate (Fin 1) :=
    { hull :=
        { volume := fun _ => -1
          hullVolume := -1
          contains := fun _ => le_rfl }
      weighted :=
        { value := fun _ => -1
          weight := fun _ => 1
          weightTotal := 1
          weightTotal_pos := one_pos
          weightTotal_eq_sum := by simp }
      weighted_matches_hull := fun _ => rfl
      weights_nonnegative := fun _ => zero_le_one
      qSigned := -2
      thetaSigned := -1
      q_le_hull := by norm_num
      hull_le_theta := by norm_num
      q_negative := by norm_num }
  exact cTheta_lower_bound_of_finiteCertificate hcert
    (q := Real.exp 2) (by rw [Real.log_exp]; norm_num [hcert])
    (by rw [Real.log_exp]; norm_num [hcert])

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the certificate-side Step (xi-f) transfer. -/
def certificateCThetaTransfer : Obligation :=
  { id := "IUT-III.StepXI.certificate-cTheta-transfer"
    source := "IUT III, Corollary 3.12 proof, Steps (xi-d)-(xi-f) " ++
      "(source-audit transcription lines 1070-1146)"
    status := VerificationStatus.proved
    note :=
      "The certificate-side transfer of the terminal Step (xi-f) bound is " ++
        "proved over any supplied StepXIFiniteCertificate: the normalized " ++
        "WeightedValues average of the hull volumes lies below thetaSigned, " ++
        "and C_Theta >= -1 follows from -|log(Theta)| <= C_Theta * |log(q)| " ++
        "once |log(q)| is identified with -qSigned. The identification and " ++
        "the source-carrier certificate are explicit inputs, not constructed " ++
        "here; the carrier realization remains with the parent obligation."
    dependsOn := [ "IUT-III.holomorphic-hull-determinant-log-volume" ] }

end LeanFormal.IUT.Audit
