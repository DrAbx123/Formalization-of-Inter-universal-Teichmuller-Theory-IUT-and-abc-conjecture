import LeanFormal.IUT.Audit.Status

/-!
# S3137: external/repo TOOL INVENTORY index (Lead discovery, task-59 maintenance)

Machine-readable index of the EXISTING mathematical tools available in the
repo, per `coord/TOOL-INVENTORY.md` sections E1-E4 and the repo-tool section,
together with the tools manufactured by this stream.  Consumers should look
for a tool here FIRST, then manufacture per Lead policy.  Data only.

External libraries registered in lakefile.toml (all built, importable with
module roots `Iut.*`, `PadicField.*`, `ContinuousKummerTheory.*`, `Brauer.*`,
`Reciprocity.*`, `ClassFieldAxiom.*`, `Galois.*`, `Herbrand.*`; NOT
`LeanFormal.IUT.*`):

* E1 `Iut` (source anabelioid/frobenioid/orbicurve foundations) — R1 source
  place/transport, first-triangle source objects;
* E2 `ContinuousKummerTheory` — canonical normalized 2l-th root supply
  (`kummerRoot`, `kummerRoot_pow`, `kummer`), Hilbert 90, ContH1;
* E3 `PadicField` — p-adic uniformizer/valuation/norm/ramification/complete
  (`Uniformizer.v_mul/v_pow/v_zpow/uniformizer_spec/IsUniformizer`, Norm,
  FieldNorm, Complete, Extension, Galois, Tower, Ramification, Unramified);
* E4 `Brauer`, `Reciprocity`, `ClassFieldAxiom`, `Galois`, `Herbrand` — local
  CFT/units/norm compatibility, conjugate/local reciprocity (F4 value group,
  first-triangle conjugate map C2).

Repo tools most relevant to the open residuals (already green):
* `LeanFormal.IUT.BaseScalarValuationRelation.lowerPrimeValuation` — valuation
  of the rational scalar p in the lower completion = exp(-1);
* `NumberFieldFinitePlace.norm_eq_absNorm_zpow` (canonical norm formula) +
  `Example36.concretePlace_lower_absNorm` (=5) +
  `Example36.concretePlace_norm_completionMap_eq` (isometry) — M2a closure
  (qpilot S3133M2aClosedActual);
* `norm_completionMap_pow` + `relativeCompletionDegree` — completion norm
  transport at the actual local degree;
* `Padic.norm_p`, `Padic.norm_p_zpow`, `Padic.norm_p_pow`;
* `haarLogVolume` interface lemmas (monotonicity, finiteness);
* Mathlib `measure_isAddInvariant_eq_smul_of_isCompact_closure`,
  `measure_isAddHaarMeasure_eq_smul_of_isOpen`,
  `integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport` — Haar uniqueness.

Tools manufactured by this stream (full proofs + probe):
* `S3137LogVolumeMapToolActual`: generic Haar log-volume transport along a
  measurable map / injective map / nonzero scalar scaling;
* `S3137PadicNormToolActual`: generic p-adic norm of the prime and its powers;
* `S3137ThetaPacketLogVolumeToolActual`: generic finite theta-packet
  log-volume closed form and sign laws.
-/

namespace LeanFormal.IUT.Audit

/-- **External library tools (E1-E4): availability and relevance.** -/
def S3137ExternalToolIds : List (String × String) :=
  [ ("TOOL.EXTERNAL.IUT.SOURCE-ANABELIOID-FROBENIOID", "Iut.* (256 files, 205 oleans): source anabelioid/frobenioid/orbicurve/finite-stage foundations, SourceFinitePlaceMLFBase adic-completion algebra instances; relevant to R1 source place/transport and first-triangle source objects."),
    ("TOOL.EXTERNAL.CKT.KUMMER-ROOT", "ContinuousKummerTheory.* (18 oleans): Mu, kummerFun, kummerCocycle, kummerRoot (HasKummerRoots.exists_pow_eq), kummerRoot_pow, kummer, Hilbert90; relevant to canonical normalized 2l-th root supply (q_v^(1/2l)) and unit/Kummer classes."),
    ("TOOL.EXTERNAL.PADIC.NORM-UNIFORMIZER", "PadicField.* (19 oleans): Uniformizer (wval, valGen, v_mul/v_pow/v_zpow, uniformizer_spec, IsUniformizer), Norm, FieldNorm, Complete, Extension, Galois, Tower, Ramification, Unramified, Teichmuller; relevant to qpilot M2a/M2b, hull completion, F4 units/valuations."),
    ("TOOL.EXTERNAL.BRAUER.LOCAL-CFT", "Brauer.* (23 oleans): KummerH2, KummerCompat, ArtinPairing, ArtinTransfer, FundamentalClass, LocalGalois, Unramified, Invariant, Duality; relevant to F4 value group and first-triangle C2 conjugate/local reciprocity."),
    ("TOOL.EXTERNAL.RECIPROCITY-ETC", "Reciprocity.* (28), ClassFieldAxiom.* (8: rho = nrm(uniformizer)^e etc), Galois.* (2), Herbrand.* (3): local CFT/norm compatibility, units, conjugate map data; relevant to F4 value group and C2.") ]

/-- **Repo tools most relevant to the open residuals.** -/
def S3137RepoToolIds : List (String × String) :=
  [ ("TOOL.REPO.LOWER-PRIME-VALUATION", "LeanFormal.IUT.BaseScalarValuationRelation.lowerPrimeValuation: valuation of the rational scalar p in the lower completion = exp(-1); M2a base computation."),
    ("TOOL.REPO.CANONICAL-NORM-FORMULA", "NumberFieldFinitePlace.norm_eq_absNorm_zpow + Example36.concretePlace_lower_absNorm (=5) + concretePlace_norm_completionMap_eq (isometry): canonical completion norm of (5:Completion) and transfer to Gaussian completion; qpilot M2a closure (S3133M2aClosedActual)."),
    ("TOOL.REPO.COMPLETION-NORM-TRANSPORT", "norm_completionMap_pow + norm_algebraMap_pow_of_finrank_eq_relativeCompletionDegree: completion norm transport at the actual local degree; R2/normalization."),
    ("TOOL.REPO.PADIC-NORM", "Padic.norm_p, Padic.norm_p_zpow, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation."),
    ("TOOL.REPO.HAAR-UNIQUENESS", "Mathlib measure_isAddInvariant_eq_smul_of_isCompact_closure, measure_isAddHaarMeasure_eq_smul_of_isOpen, integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport, addHaarScalarFactor lemmas; relevant to abc S3135HaarUniquenessScalarStep / F4(b1)."),
    ("TOOL.REPO.HAAR-LOG-VOLUME", "LeanFormal.IUT.NumberFieldFinitePlace.haarLogVolume + haarLogVolume_of_lt_top/eq_zero_of_null/mono; normalization streams.") ]

/-- **Tools manufactured by this stream (fully proved, probe-verified).** -/
def S3137ManufacturedToolIds : List (String × String) :=
  [ ("TOOL.S3137.LOG-VOLUME-MAP", "S3137LogVolumeMapToolActual: haarLogVolume_map_of_preimage_eq, haarLogVolume_map_image_of_injective, haarLogVolume_map_const_smul_image (generic Haar log-volume transport/scalar-scaling invariance)."),
    ("TOOL.S3137.PADIC-NORM", "S3137PadicNormToolActual: padic_norm_prime, padic_norm_prime_zpow, padic_norm_prime_pow, padic_prime_ne_zero, exists_padic_norm_prime_inv, padic_norm_five."),
    ("TOOL.S3137.THETA-PACKET-LOGVOLUME", "S3137ThetaPacketLogVolumeToolActual: finiteThetaPacket_logVolume_eq_weight_mul_log, _ofQ_eq, _nonpos_of_q_le_one, _neg_of_q_lt_one.") ]

/-- All tool ids indexed (external + repo + manufactured). -/
def S3137ToolInventoryIndex : List (String × String) :=
  S3137ExternalToolIds ++ S3137RepoToolIds ++ S3137ManufacturedToolIds

theorem S3137ToolInventoryIndex_length :
    S3137ToolInventoryIndex.length = 14 := rfl

end LeanFormal.IUT.Audit