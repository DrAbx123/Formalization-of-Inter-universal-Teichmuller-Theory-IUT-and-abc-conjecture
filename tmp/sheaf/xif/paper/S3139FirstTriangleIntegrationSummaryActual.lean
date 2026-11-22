/-!
# S3139: first-triangle integration — summary, residual list, ownership (component documentation)

Final assembly of the first triangle (BPS -> multiradial representation) from
the constructed components, as a conditional theorem
(@firstTriangleConditional@, @publicFirstTriangleConditional@).

## Assembled components

* field (A): @sourceRealCapsuleContract@ / the source-anchored capsule contract;
  exact residual @SourceCapsuleSourceDataMissing@ (the (Ind1)/C3 dependency);
* field (B): @sourceLGPData@ — SourceLGPData from the ACTUAL source Theta values
  (splitting monoid = closure of the actual Theta-packet special values), its
  theta-generator membership, P2/P1 compatibility;
* field (C): the archimedean realified copy action — @sourceFmodArchimedeanLog@,
  @sourceFmodArchimedeanScalarCharacter@, @SourceArchimedeanRealification@,
  @sourceArchimedeanCopyActionData@ (preserves splitting-monoid scalar action);
* C2 (reduced): the completion-level global-units maps
  (@sourceFmodUnitsToFiniteCompletion@, @sourceFmodUnitsToInfiniteCompletion@)
  and the realified degree/scalar channel (@SourceFmodLocalElementMap.localDegree@,
  @localScalarUnit@); the finite-place copy action
  (@sourceFinitePlaceCopyActionData@, @SourceCopyActionChannels@).  After
  stage4's lgpGlobalUnitsToLocalUnits (S3136LGPGlobalUnitsToLocalUnitsActual),
  C2 has NO independent missing data: it reduces to the cross-stream
  identifications M0/R1 (same-C F ~ F_mod) and M1/R1 (place selection
  V -> C3.tensorIndex);
* mutation and readout: @sourceMultiradialMutation@ (with gluing-witness
  invariance, the paper's indeterminate input), the post-mutation q-pilot
  log-volume @sourceQPilotSignedLog@ = -|log q| (negative from q != 1), and the
  q/Theta seam @sourceQThetaComparisonInputFromTheta@ into the S3138 source V2
  boundary, giving the Corollary 3.12 ordered conclusion
  (@firstTriangleConditional@).

## Remaining residual (reduced)

* C1: source infinite-place choice, @SourceInfinitePlaceChoice@ (III:616-620;
  InitialThetaArithmeticData has no infinite-place field; any supplied choice
  yields the actual channel);
* C3: tensor-factor identification, @SourceInd1BridgeDependency@ (depends on
  field (A) source capsule data);
* cross-stream: M0/R1 same-C identification (lattice/mainline), M1/R1 place
  selection (qpilot place-index files), with stage4's
  S3136LGPGlobalUnitsToLocalUnitsActual unit map and its
  LGPGlobalUnitsLocalMissing {sameCIdentification, placeSelection, ...};
* fourth-triangle inputs: signed Theta-hull value and (xi-f) inclusion
  (shehdd stream); the first triangle supplies only the q-side.

## Consumers and registry

@publicFirstTriangleConditional@, @firstTriangleResidualObligationIds@,
@firstTriangleConstructedIds@ (S3139FirstTriangleIntegrationConsumerActual);
messages sent to lattice and mainline.  No sorry/axiom/True/PUnit/toy carrier.
-/
