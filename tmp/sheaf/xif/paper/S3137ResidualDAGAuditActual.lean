import LeanFormal.IUT.Audit.Status

/-!
# S3137: residual-DAG acyclicity / self-reference audit + trivial-scaling audit (task-68/69 input)

Machine-checkable audit data for the canonical residual index.  Result:
(1) all dependency edges go from a sub-node to a PARENT registry id or to an
    INDEX node of STRICTLY SMALLER depth (acyclic certificate, checked below);
(2) no node's dependsOn list contains itself;
(3) no index node references `F4.c.cardP` / `ABCConjecture` / `cor312`: the only
    occurrences are classification text (`F4.c.cardP-ABC-strength` is documented
    as the sole ABC-strength node), never a dependency or a statement of another
    node;
(4) R1 nodes (M1 anchor/M2a/M2b/Tate-q/status-note) depend only on the registry
    parents R1.M2M3M5 / R1.M0 / R1.M1; they do NOT reference each other's missing
    data (M2b Tate-q does not mention M2a, M2a does not mention M2b);
(5) trivial-scaling audit: `scaling := 1` is a model-instance field
    (SourceUnitRegionHaarDataActual.lean:421; SourceContractedSupplyRealization:226;
    OModuleCompactnessLayer:197).  `sourceHaarActual_scalingLogDegree_zero` is
    proved only for the concrete model (`sourceHaarActualOriginalInput S`, arbitrary
    D over that model) and the concrete gate theorem is explicitly model-scoped
    (`s3135_finalAssemblyGateV4_concreteModel`, with F4.a + F4.c.cardP still
    hypotheses).  The general gate/final-assembly theorems keep the general
    residuals as hypotheses; the trivial concrete scaling is NOT used to prove
    the general F4(b) residual.  FLAG (non-circular, but evidence-scope): the
    concrete normalized model is not paper evidence for the general
    F4.b.paper-scaling-zero residual, which stays OPEN (except b1 partial).
Data only; no proof content beyond the mechanical checks.  WRITE-ONLY.
-/

namespace LeanFormal.IUT.Audit

/-- Dependency edges of the index sub-nodes (source -> targets), from the part
files' `dependsOn` fields; parent registry ids are depth-0 roots. -/
def S3137IndexDependencyEdges : List (String × List String) :=
  [ ("INDEX.ThetaHalf.canonical-rooted-readout",
      ["INDEX.ThetaHalf.vform-canonical-identification",
       "INDEX.ThetaHalf.normalization-factor-zero", "ThetaHalf.exact-factor-residual"]),
    ("INDEX.F4.b1.haar-uniqueness-scalar-step",
      ["F4.b.paper-scaling-zero", "INDEX.F4.b1.additive-haar-modulus-law"]),
    ("INDEX.F4.b1.log-shell-scaling-index",
      ["F4.b.paper-scaling-zero", "INDEX.F4.b1.additive-haar-modulus-law"]),
    ("INDEX.FT.C2.conjugate-copy-action",
      ["first-triangle.A-C", "INDEX.FT.C2.local-element-map",
       "INDEX.FT.C2.fiber-assignment"]),
    ("INDEX.FT.C2.reduces-to-M0-M1",
      ["first-triangle.A-C", "R1.M0.native-to-OriginalInput",
       "R1.M1.bad-tensor-index", "LGP.residuals"]),
    ("INDEX.FT.C2.kummer-artin-pairing",
      ["first-triangle.A-C", "INDEX.TOOL.brauer-pairing"]),
    ("INDEX.ThetaHalf.final-composition",
      ["ThetaHalf.vform-canonical-residual", "ThetaHalf.exact-factor-residual",
       "INDEX.R1.C3-place-tie"]),
    ("INDEX.R1.M2b.tate-q-identification", ["R1.M2M3M5.sameC-q-theta-readout"]),
    ("INDEX.R1.status-note", ["R1.M2M3M5.sameC-q-theta-readout"]),
    ("INDEX.R1.C3-place-tie", ["R1.M2M3M5.sameC-q-theta-readout"]),
    ("INDEX.R1.M2.base-q-transport", ["R1.M2M3M5.sameC-q-theta-readout"]),
    ("INDEX.R1.M2.clause-B-descent", ["R1.M2M3M5.sameC-q-theta-readout"]) ]

/-- Depth certificate: parents at 0, first-level INDEX nodes at 1, nodes that
depend on them at 2.  Every edge must strictly decrease depth. -/
def S3137IndexDepths : List (String × Nat) :=
  [ ("R1.M2M3M5.sameC-q-theta-readout", 0), ("R1.M0.native-to-OriginalInput", 0),
    ("R1.M1.bad-tensor-index", 0), ("ThetaHalf.vform-canonical-residual", 0),
    ("ThetaHalf.exact-factor-residual", 0), ("F4.b.paper-scaling-zero", 0),
    ("LGP.residuals", 0), ("first-triangle.A-C", 0), ("INDEX.TOOL.brauer-pairing", 0),
    ("INDEX.ThetaHalf.vform-canonical-identification", 1),
    ("INDEX.ThetaHalf.normalization-factor-zero", 1),
    ("INDEX.F4.b1.additive-haar-modulus-law", 1),
    ("INDEX.FT.C2.local-element-map", 1), ("INDEX.FT.C2.fiber-assignment", 1),
    ("INDEX.R1.C3-place-tie", 1), ("INDEX.R1.M2.base-q-transport", 1),
    ("INDEX.R1.M2.clause-B-descent", 1), ("INDEX.R1.M2b.tate-q-identification", 1),
    ("INDEX.R1.status-note", 1),
    ("INDEX.ThetaHalf.canonical-rooted-readout", 2),
    ("INDEX.F4.b1.haar-uniqueness-scalar-step", 2),
    ("INDEX.F4.b1.log-shell-scaling-index", 2),
    ("INDEX.FT.C2.conjugate-copy-action", 2),
    ("INDEX.FT.C2.reduces-to-M0-M1", 2),
    ("INDEX.FT.C2.kummer-artin-pairing", 2),
    ("INDEX.ThetaHalf.final-composition", 2) ]

/-- **Mechanical check: no self-reference** (no edge's source appears in its
targets). -/
theorem S3137Index_no_self_reference :
    S3137IndexDependencyEdges.all (fun e => !(e.2.contains e.1)) = true := by
  decide

/-- **Mechanical acyclicity certificate**: every dependency target is a
registered node/parent and has strictly smaller depth than the source, so the
dependency graph is acyclic (no cycle can strictly decrease depth). -/
def S3137DepthOf (s : String) : Nat :=
  (S3137IndexDepths.find? (fun p => p.1 == s)).map (fun p => p.2) |>.getD 0

theorem S3137Index_depth_strict :
    S3137IndexDependencyEdges.all
      (fun e => e.2.all (fun t => decide (S3137DepthOf t < S3137DepthOf e.1))) = true := by
  decide

/-- **Audit result: residual-DAG acyclicity / self-reference.** -/
def S3137ResidualDAGAudit : Obligation :=
  { id := "S3137.audit.residual-dag-acyclicity"
    source := "S3137CanonicalResidualIndexPart1..14; S3137ResidualIndexParentMapActual; coord/TOOL-INVENTORY.md"
    status := VerificationStatus.interface
    note := "PASS: (1) dependency edges are sub-node -> parent registry id or INDEX node of strictly smaller depth; S3137Index_no_self_reference and S3137Index_depth_strict are kernel-checked by decide, giving an acyclicity certificate (no cycle can strictly decrease depth); (2) no node references F4.c.cardP/ABCConjecture/cor312 in statement or dependsOn (occurrences are classification text only); (3) R1 nodes (M1 anchor/M2a/M2b/Tate/status-note/C3-tie) depend only on registry parents R1.M2M3M5/M0/M1, no mutual missing-data references; (4) INDEX-only cross references: ThetaHalf canonical-rooted->vform+normalization; F4.b1 haar/scaling->additive-law; FT.C2 conjugate->local-element+fiber; FT kummer-artin->brauer tool; ThetaHalf final-composition->vform+exactfactor+C3-tie; all acyclic."
    dependsOn := ["S3137CanonicalResidualIndexActual", "S3137ResidualIndexParentMapActual"] }

/-- **Audit result: trivial-scaling model scope (abc input-trivialization flag).** -/
def S3137TrivialScalingAudit : Obligation :=
  { id := "S3137.audit.trivial-scaling-model-scope"
    source := "LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean:421; SourceContractedSupplyRealization.lean:226; OModuleCompactnessLayer.lean:197; S3135ScalingActualModelActual; S3135GateV4ConcreteModelActual"
    status := VerificationStatus.interface
    note := "FINDING (non-circular INPUT-FIDELITY flag; abc exhaustive audit): there are EXACTLY 3 SourceUnitRegionHaarData constructors in the repo — SourceUnitRegionHaarDataActual.lean:421, SourceContractedSupplyRealization.lean:226, OModuleCompactnessLayer.lean:197 — and ALL three set `scaling := 1`: there is NO nontrivial-lambda instance.  Consequently S3135ScalingLogDegreeZero is trivial for every instance, and the nontrivial F4(b) remains flagged PAPER INPUT.  `scaling := 1` is a concrete model-instance field;  sourceHaarActual_scalingLogDegree_zero is proved only for the concrete model sourceHaarActualOriginalInput S with arbitrary D over that model (uses D's hull_subset_scaledRegionImage, not scaling:=1 directly).  The concrete gate V4 theorem s3135_finalAssemblyGateV4_concreteModel is explicitly model-scoped and keeps F4.a + F4.c.cardP as hypotheses; general gate/final-assembly theorems keep the general residuals as hypotheses, so the trivial concrete scaling is NOT used to prove the general F4(b) residual.  FLAG: the concrete normalized model is not paper evidence for general F4.b.paper-scaling-zero (stays OPEN except b1 partial); consumers must not cite the concrete instance as the general residual.  Also noted: (logShellScale)^{-1} has norm p, not a Z_p unit scalar (abc)."
    dependsOn := ["S3135ScalingActualModelActual", "S3135GateV4ConcreteModelActual"] }

end LeanFormal.IUT.Audit