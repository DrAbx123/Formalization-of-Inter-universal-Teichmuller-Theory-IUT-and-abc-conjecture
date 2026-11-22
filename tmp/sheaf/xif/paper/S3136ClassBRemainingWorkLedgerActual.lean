/-! # Stage-4 host: class-B remaining work ledger (concrete plans)

Data ledger of the remaining class-B formalization work for the (c) estimate and
the paper route, each item with its exact corpus location, the concrete
construction plan, the artifact that will consume it, and the current status.
No abstract bookkeeping: every row names a concrete Lean target.

LABEL: work ledger (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136ClassBRemainingWorkLedgerActual

structure LGPClassBWorkRow where
  item : String
  corpusCitation : String
  concretePlan : String
  consumerArtifact : String
  status : String

def lgpClassBRemainingWork : List LGPClassBWorkRow :=
  [ ⟨"log-shell tensor estimates (Prop 1.4)", "IUT IV p.656-757", "formalize log-volume of arithmeticTensorTupleBlock lattices using native Haar family + arithmeticTupleNormalizedLogVolume; prove the (ii) estimate for the actual Gaussian tensor packet", "S3136ClassARegionVolumeBoundToolActual / S3136ModelThetaTensorVolumeFiniteActual", "missing classB; classA volume tools ready"⟩,
    ⟨"archimedean metric estimates (Prop 1.5)", "IUT IV p.822-900", "archimedean analogue on the complexification; needs a complex Haar/volume setup not yet in tree", "none yet", "missing classB"⟩,
    ⟨"weighted averages over labels (Prop 1.7)", "IUT IV p.927-1010", "prove average-of-log-sums identity over SignedLabel l; reuse LGP label weights and torus-action symmetry (lgpThetaLabelWeight, gaussExponent)", "S3136ModelThetaPacketLawsActual / LGP label-weight files", "missing classB; classA label data ready"⟩,
    ⟨"(R1)-(R3) prime-splitting/rounding estimates (split point bound)", "IUT IV p.1523-1545", "formalize log(e_v) bounds from ramification indices and local fields; uses local-field different/conductor theory", "state needs local CFT/valuation API from tmp/local-cft-port", "missing classB"⟩,
    ⟨"holomorphic-hull log-volume upper bound (unit-region bound)", "IUT IV p.1586-1680", "bound normalizedLogVolume of thetaTensorHull by the theta coefficient sum; use arithmeticTupleNormalizedLogVolume + compactness + the C_Theta shape", "S3136ModelThetaTensorVolumeFiniteActual / S3136IVThm110ConstantsActual", "missing classB; classA compactness/volume ready"⟩,
    ⟨"final Theorem 1.10 assembly (C_Theta formula p.1363-1385)", "IUT IV p.1363-1385", "combine (ii),(iv),(v) estimates with the exact constants d*_mod/e*_mod/eta_prm (already formalized) to derive the final display", "S3136IVThm110ConstantsActual.lgpThm110DisplayShape", "missing classB; shapes ready"⟩,
    ⟨"Cor 2.2 (ii)/(iii) consequences + (C1),(C2)", "IUT IV p.2426-2505", "derive the estimate on Exc_d from Theorem 1.10 via elementary log manipulations (class A part: PNT/Prop 2.1 linearization)", "S3136Cor22MainEstimateShapeActual / S3136Cor22ConditionsShapeActual", "missing classB"⟩,
    ⟨"Cor 2.3/Thm A reduction", "IUT IV p.3117-3155", "apply the [GenEll] Thm 2.1 equivalence shape to the Cor 2.2 (i)-(iii) inputs; class A reduction step", "S3136PaperInputStatementHooksActual / S3136GenEllReductionShapeActual", "reduction hook ready; awaits Cor 2.2"⟩ ]

theorem lgpClassBRemainingWork_length : lgpClassBRemainingWork.length = 8 := rfl

#check lgpClassBRemainingWork
#check lgpClassBRemainingWork_length

end LeanFormal.IUT.XiFPaper.S3136ClassBRemainingWorkLedgerActual