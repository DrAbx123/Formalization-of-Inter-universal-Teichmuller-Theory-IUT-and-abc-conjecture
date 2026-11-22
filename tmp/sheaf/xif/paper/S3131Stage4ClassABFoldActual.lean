import LeanFormal.IUT.Audit.Status

/-! # S3131 stage4 class A/B source classification folded (data only) -/

namespace LeanFormal.IUT.XiFPaper.S3131Stage4ClassABFoldActual

def S3131Stage4ClassABFold : List (String × String) :=
  [ ("class A", "IUT IV Prop 2.1 p.2334; Cor 2.2(i) p.2404-2428 (proof p.2506-2529); Cor 2.3/Thm A reduction p.3117-3155; [GenEll] Thm 2.1 p.615; [Mzk1]"),
    ("class B", "Thm 1.10 p.1255 final display p.1363-1385; Steps (iii)-(vi) p.1523-1545 (R1)-(R3); hull log-vol p.1586-1680; weighted avgs p.1710-1783; Cor 2.2(ii) p.2426-2493; Cor 2.2(iii) p.2494-2505; Props 1.4-1.7 p.400-1060"),
    ("(c) unit-region bound", "Thm 1.10 holomorphic-hull log-volume estimate + final display (class B)"),
    ("(c) split point bound", "Thm 1.10 Steps (iii)-(v) (R1)-(R3) + weighted averages (class B)"),
    ("GenEll role", "REDUCTION ONLY; not ABC proof, not IUT-side estimate"),
    ("stage4 files", "S3136RegionEstimateSourceClassificationActual (10 rows); S3136GenEllPaperStatementsActual (8 rows: Def 1.1 p.112, Def 1.2 p.213, Ex 1.3 p.231, Prop 1.4 p.294, Def 1.5 p.432, Prop 1.6 p.505, Prop 1.7 p.524, Thm 2.1 p.615)") ]

theorem S3131Stage4ClassABFold_length : S3131Stage4ClassABFold.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.S3131Stage4ClassABFoldActual