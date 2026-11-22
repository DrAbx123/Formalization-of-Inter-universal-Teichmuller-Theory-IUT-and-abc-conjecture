/-! # Stage-4 host: map of the IUT IV Theorem 1.10 proof steps to needed components

TEXT: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt;
Theorem 1.10 statement p.1255-1385, proof p.1386-2291 (Steps (i)-(vi)).

CONSUMER: mainline's IUT IV statement skeleton. This data map records, for each
proof step of Theorem 1.10, the formal component it requires and which stream
piece currently supplies it or what remains. This is the (c) split point/unit-region
bound work breakdown at the exact paper granularity.

LABEL: proof-step map (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136ClassBProofStepMapActual

structure LGPThm110StepRow where
  step : String
  lineRange : String
  neededComponent : String
  suppliedByOrMissing : String

def lgpThm110ProofStepMap : List LGPThm110StepRow :=
  [ ⟨"setup: collections of initial Theta-data, fields F_mod,F_tpd,F, divisors q,f, log(q),log(f)", "1255-1385", "SourceNativeInitialThetaData + Theta-packet + model clause data", "conditional clause data (LGPModelSourceClauseMissing / LGPConcreteClauseData) + concrete Theta packet (done)"⟩,
    ⟨"Step (i): deformation/prime-strip setup, Frobenius-like objects", "1386-1520 approx", "Hodge theater/prime-strip data", "lattice/qpilot streams (theater/palette); S3136ModelThetaPacketActual supplies Theta slot"⟩,
    ⟨"Step (ii): evaluation-inclusion/rounding estimates (R1)-(R3) for log(e_v)", "1523-1545", "prime-splitting/rounding bounds = (c) SPLIT POINT BOUND", "MISSING class B (formalization target; no stream piece yet)"⟩,
    ⟨"Step (iii): log-shell tensor/pilot object estimates, C_Theta bound (formula p.1363-1375)", "1545-1584", "Theta-pilot log-volume estimates + constants d*_mod/e*_mod/eta_prm", "constants done in S3136IVThm110ConstantsActual; log-volume estimates MISSING class B"⟩,
    ⟨"Step (iv)-(v): holomorphic-hull log-volume upper bounds and weighted averages", "1586-1783", "region-family log-volume bound = (c) UNIT-REGION BOUND + weighted averages", "native Haar family (done) + theta regions/hulls (done) + IsBDLe tool (done); the bound itself MISSING class B"⟩,
    ⟨"Step (vi): assembly of final displays p.1376-1385", "1784-2291", "summation of bounds with constants", "class A arithmetic available (S3136IVThm110ConstantsActual); needs (ii),(iv),(v)"⟩,
    ⟨"Cor 2.2 (ii)/(iii): consequences for the compactly bounded set (conditions (C1),(C2))", "2380-2505", "Thm 1.10 + elementary log manipulations + PNT", "class B; shapes recorded, proofs missing"⟩,
    ⟨"Cor 2.3 / Theorem A: reduction to [GenEll] Thm 2.1 (ii)", "3117-3155", "[GenEll] Thm 2.1 equivalence + Cor 2.2 (i)-(iii)", "class A reduction shape done (S3136GenEllReductionShapeActual / statement hooks); needs Cor 2.2 (ii),(iii)"⟩ ]

theorem lgpThm110ProofStepMap_length : lgpThm110ProofStepMap.length = 8 := rfl

#check lgpThm110ProofStepMap
#check lgpThm110ProofStepMap_length

end LeanFormal.IUT.XiFPaper.S3136ClassBProofStepMapActual