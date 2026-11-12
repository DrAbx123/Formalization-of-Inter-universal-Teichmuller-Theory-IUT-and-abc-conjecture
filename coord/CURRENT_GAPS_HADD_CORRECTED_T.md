# Current gaps — hadd upper estimate and corrected T

Date: 2026-11-07. Policy: no simplification; construct missing objects; teammates may
freely use subagents. No placeholders/True/PUnit/fake axiom.

## A. hadd upper estimate

Status: OPEN.

- hadd is NOT an input; it must not be assumed.
- Existing CTheta results are LOWER bounds only.
- Required: UPPER estimate on the theta/log-volume side.
- S2919ThetaUpperFromProcession is CONDITIONAL: it takes `ThetaUpperCertificate`
  and returns the upper bound. The certificate is not constructed.
- S2920ThetaLinkHeight gives only statement/thetaLink laws
  (`S2920HeightLeProcession`, `S2920_thetaLink_generator`,
  `S2920_thetaLink_unitPower`), not the bridge.
- EXACT MISSING: height/thetaLink bridge connecting `HeightLeProcession` and
  `thetaLink`; without it the certificate cannot be discharged.

## B. Corrected T

Status: OPEN.

- Old `unique_elliptic_involution` field is FALSE (S2875 actual): it forces
  `ellipticInvolution = identity`; a nontrivial involution is impossible on the
  old schema.
- Old SourceCompletion chain CANNOT directly consume corrected A6.
- Need a CORRECTED DOWNSTREAM construction.
- Actual now: S2908CorrectedSActual; S2907CorrectedCompletionInputs partial
  (4 fields).
- S2907b: restate S2817/S2846 clause scaffold on corrected structure, split in
  two steps. ClauseD/E can be actual first; ClauseF needs corrected A/B/C/D.
- kSide / localFamily / boundary need corrected restatement; NO forgetful
  conversion to old SourceSignQuotientData S.
- 11 consumers still pending corrected adaptation.
- S2921-S2926 in progress/assigned; no completed corrected T yet.

## C. What is NOT acceptable

- Reusing old unique-field consumers as if they consumed corrected A6.
- Forgetful map back to old S.
- Treating S2919/S2920 statements as the missing hadd bridge or certificate.
- Assuming hadd, ABC, or a placeholder object.
