import LeanFormal.IUT.Audit.Status

/-! # S3131 endgame class A / class B node lists (citations) -/

namespace LeanFormal.IUT.XiFPaper.S3131EndgameClassABListsActual

def S3131ClassANodes : List (String × String) :=
  [ ("IUT IV Prop 2.1 p.2334", "log x <= x / PNT bounds"),
    ("IUT IV Cor 2.2(i) p.2404-2428 (proof p.2506-2529)", "BD-class equalities; [GenEll] Prop 1.4(i),(iii) + degree-6"),
    ("IUT IV Cor 2.3 / Thm A reduction p.3117-3155", "given Cor 2.2(ii),(iii)"),
    ("[GenEll] Thm 2.1 p.615", "equivalence (i)<=>(ii); reduction (ii)=>(i)"),
    ("[Mzk1] Noncritical Belyi Maps", "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt") ]

def S3131ClassBNodes : List (String × String) :=
  [ ("IUT IV Thm 1.10 p.1255 final display p.1363-1385", "log-volume estimates for Theta-pilot objects"),
    ("Thm 1.10 Steps (iii)-(vi) p.1523-1545 (R1)-(R3)", "prime-splitting/rounding estimates"),
    ("Thm 1.10 holomorphic-hull log-volume p.1586-1680", "unit-region bound side"),
    ("Thm 1.10 weighted averages p.1710-1783", "weighted-average side"),
    ("Cor 2.2(ii) p.2426-2493 (C1),(C2) p.2475-2493", "main estimate"),
    ("Cor 2.2(iii) p.2494-2505", "refinement"),
    ("IUT IV Props 1.4-1.7 p.400-1060", "elementary/technical props") ]

theorem S3131ClassANodes_length : S3131ClassANodes.length = 5 := rfl
theorem S3131ClassBNodes_length : S3131ClassBNodes.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.S3131EndgameClassABListsActual