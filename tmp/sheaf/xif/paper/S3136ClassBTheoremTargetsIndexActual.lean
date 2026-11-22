/-! # Stage-4 host: index of class-B theorem targets for the paper route

TEXT: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt;
papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt.

CONSUMER: mainline's IUT IV statement skeleton / FINAL-STATUS. Data index of the
class-B targets (proved in paper, formalization targets) with their exact corpus
citations, needed inputs, and the stage-4 artifacts already supplying hypotheses.

LABEL: index (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136ClassBTheoremTargetsIndexActual

structure LGPClassBTargetRow where
  target : String
  corpusCitation : String
  neededInputs : String
  suppliedPieces : String
  status : String

def lgpClassBTheoremTargets : List LGPClassBTargetRow :=
  [ ⟨"Theorem 1.10 (log-volume estimates for Theta-pilot objects)", "IUT IV p.1255-1385 (final display p.1363-1385)", "initial Theta-data; Theta-pilot objects; log-shell tensor estimates; (R1)-(R3); weighted averages", "S3136ModelThetaPacketActual (Theta slot); S3136NativeHaarFamilyActual (Haar); S3136IVThm110ConstantsActual (constants/formula shapes)", "classB target"⟩,
    ⟨"Prop 1.4 (nonarchimedean normalized log-volume estimates)", "IUT IV p.656-757", "log-volumes of tensor products of log-shells", "native Haar family + compact-region finiteness (S3136ModelThetaTensorVolumeFiniteActual)", "classB target"⟩,
    ⟨"Prop 1.5 (archimedean metric estimates)", "IUT IV p.822-900", "archimedean log-volume estimates", "not supplied by mod-side data (archimedean analytic input)", "classB target"⟩,
    ⟨"Prop 1.7 (weighted averages)", "IUT IV p.927-1010", "averaging over labels j", "LGP theta label weights/label sums (existing LGP components)", "classB target"⟩,
    ⟨"Cor 2.2 (ii) main estimate", "IUT IV p.2426-2444 (+ (C1),(C2) p.2475-2493)", "Theorem 1.10 + elementary logs + PNT", "shapes recorded (S3136Cor22MainEstimateShapeActual / S3136Cor22ConditionsShapeActual); Thm 1.10 missing", "classB target"⟩,
    ⟨"Cor 2.3 / Theorem A (Diophantine inequalities)", "IUT IV p.3117-3155; p.93-112", "[GenEll] Thm 2.1 equivalence + Cor 2.2 (i)-(iii)", "class A reduction hooks (S3136PaperInputStatementHooksActual, S3136GenEllReductionShapeActual); shapes only", "classB modulo Cor 2.2"⟩,
    ⟨"[GenEll] Thm 2.1 reduction", "GenEll p.615-687", "compactly bounded case + [Mzk1] noncritical Belyi maps", "LGPGenEllEquivalence shape (class A); statement details indexed", "proved in paper; formalizable"⟩ ]

theorem lgpClassBTheoremTargets_length : lgpClassBTheoremTargets.length = 7 := rfl

#check lgpClassBTheoremTargets
#check lgpClassBTheoremTargets_length

end LeanFormal.IUT.XiFPaper.S3136ClassBTheoremTargetsIndexActual