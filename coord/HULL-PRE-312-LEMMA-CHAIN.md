# HULL PRE-3.12 LEMMA CHAIN (hull 算子层, bottom layer before IUT III Cor 3.12 total proof)

Registry frozen 14041. Owner: hull. Status: planning + H1/H2 implemented (Hull01/Hull02); H3-H7 staged.

Corpus: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt,
Remark 3.9.5 (corpus 7648-8300) and (Ob1)-(Ob9) (corpus ~1e4 region; see below).

| Step | Item | Corpus | Current assets | Class | Missing |
|---|---|---|---|---|---|
| H1 | hull := lambda*O (all components nonzero), least containing region; whole IQ if not rel. compact; existence/uniqueness | Rem 3.9.5(i) 7652-7680; Prop 3.9(i) 6838-6860 | tmp/sheaf/xif/paper/C3LogShellTensorHolomorphicHullActual.lean:54-99 (actualUnitRegion/actualScaledRegion/actualCandidateHulls/actualHolomorphicHull + contains/least theorems); lean C3 hull instance | A (def + uniqueness); existence for concrete C3 = paper input? | least-element existence in the lambda-O family for general region (paper asserts; ours defines as intersection); new: Hull01DefinitionActual abstract HullSystem (family closed under intersections) + hull/contains/least/unique/idempotent |
| H2 | closure operator phi: phi(P)=intersection of hulls containing P; extensive/monotone/idempotent; compatible with inclusion | Rem 3.9.5(ii) | new Hull02ClosureOperatorActual (closure laws proved abstractly); C3 concrete hull theorems | A | none for abstract laws; identification phi = paper's phi (uses H1) |
| H3 | Phi/Xi sets: Phi(P)={H | phi(P) superset H, mu_log(H)>=mu_log(P)}, Xi likewise equal; phi(P) in Phi(P); Xi-non1; compactness of indeterminacy; H_Phi/H_Xi subset phi(P) | Rem 3.9.5(iii)-(iv) | CardHullRealGeometryGapCards:62 (lambda.O scaling classes); CardHullRealGeneratorNonpositivity:56; S3132 V-form scaling (RootedScalingDecomposition/log-volume) | A/B | set-level Phi/Xi definitions over Hull01 + log-volume monotonicity API (needed: mu_log(H) monotone for inclusion — tree has arithmeticTupleNormalizedLogVolume_mono) |
| H4 | diamond-formalism + quotient identification; equivalence H1,H2 subset phi(P); bounded family phi(P_B)=intersection over beta | Rem 3.9.5(v)(vi) | SourceProcessionStepXI (xi-*); SourceProcessionStepXIInclusionResidual | A/B | set-theoretic diamond + quotient; bounded-family hull commutation |
| H5 | hull -> arithmetic vector/line bundle: O^x-stabilization; det tensor M(-)^{otimes n} weighted positive; O(-)^{-1} normalization; Ob3-3 det/log-volume consistency | (Ob1)-(Ob4) | HullDeterminantLogVolumeReduction.lean:123/153/173/179/187/197 (HullDeterminantLogVolumeFrozenSpec, matrixLogDet laws); CardAMPLThetaBoundSupply; CardHullRealSignedLogVolume | A/B | O^x-stabilization of hull; det/log-volume consistency link to frozen spec |
| H6 | Ob5/Ob6: bounded-family hull independence; mu_log(H_Phi(P))=mu_log(phi(P)) not mu_log(P); Ob7 why log-volume alone insufficient (log-Kummer constraints) | (Ob5)-(Ob7) | CardHullRealGeometryReduction (holomorphic hull generator structure); S3132 theta-hull scaling | B | exact equality statement + Ob7 record |
| H7 | Ob9/log-link compatibility: domain/codomain hull log-volume difference; arbitrary log-link iterates do not affect comparison | (Ob9); Rem 3.9.4 ~7151 | CardQCMPComparison:50-68 (frozen obstacles); sourceHullNormalizationConditionalClosure; stepxi Indet chain | B/C | log-link iteration invariance; coordinate with stepxi/stage4 |

Order of attack: H1/H2 (done: Hull01DefinitionActual, Hull02ClosureOperatorActual) -> H3 -> H4 -> H5 -> H6 -> H7.
Honesty: H3-H7 are abstractions/records or class-B named inputs; no closure claims; registry 14041.
## UPDATE 2026-11-10 07:27 (hull self-write gate)
- H1/H2 (abstract): Hull01DefinitionActual (green, CITABLE 8 decls), Hull02ClosureOperatorActual (green, CITABLE 9), Hull03PhiXiActual (green, CITABLE 9) + probe _HullPre312ProbeActual green.
- H4 certificate wiring: Hull04CertificateWiringActual green, CITABLE 5576B 7 decls (mainline gate: H4 CLOSED). CardQCMPComparison:50-68 boundary + CardAMPL shape as named class-B; wiring proved.
- H2 concrete row: Hull05WeightedIdentityActual final fix queued (explicit-scaling route: RootedScalingDecomposition at lgpNativeHaarFamily + scalar-match => ModelWeightedRootedIdentity, avoiding the eta/instance mismatch of the earlier sharpResidual route); prior compiles red with the eta mismatch; awaiting watchdog.
- H6: GAP by design (needs [Mzk1] import; mainline/stage4). H7: CLOSED (AbsTopIII14FieldScalingActual green 4202B 5 decls + bundle/probe/Hull03PhiXi).
### UPDATE 2026-11-10 13:10 (hull H5/H7 rows after resume batch 2)
- H5: DONE via reuse - O^x-stabilization PROVED (CardHullRealGeometryReduction:94), hull generator characterization (:108), det tensor bookkeeping witness (HullDeterminantLogVolumeReduction:483), Step (xi-f) ray (:501/:505); Hull09H5GapsActual CITABLE 6 decls; class-B leftovers: full O(-)^{-1} normalization + hull<=image volume (report section 17 R9/R10).
- H7/Ob9: DONE at class level - Hull08Ob9LogLinkActual (Indet05) CITABLE 5 decls; Hull10H7Ob9ConsumerActual consumes stepxi Indet06H7Ob9WiringActual (all fields) + S3182, CITABLE 5 decls; class-B leftover: arbitrary log-link iterate independence (deep Ob9).
- H6: PARTIAL by design (Mzk1/GenEll); Hull07H6InterfaceActual conditional consumer CITABLE 4 decls.
- [EtTh]: EtTh08/09 class A transformation package increments CITABLE 11/7 decls.
