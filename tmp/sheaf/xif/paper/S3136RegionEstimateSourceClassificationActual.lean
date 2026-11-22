/-! # Stage-4 host: (c) estimate source classification (IUT IV Sections 1-2)

TEXT: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt

Exact sources:
* Theorem A (p.93): Diophantine inequalities for hyperbolic curves (the endpoint).
* Theorem 1.10 (p.1255, final display p.1363-1385): log-volume estimates for
  Theta-pilot objects; final inequality
  (1/6) log(q) <= (1 + 20 d_mod/l)(log(d_Ftpd) + log(f_Ftpd)) + 20(e*_mod l + eta_prm)
  <= ... (the IUT-side undilated region/log-volume estimate).
* Cor 2.2 (p.2380): (i) BD-class equalities (1/6)log(q-non2) ~ (1/6)log(q-forall)
  ~ (1/6)ht_inf ~ ht_omega_X(D) on K_V (proof p.2506-2529 uses only [GenEll],
  Prop 1.4 (i),(iii) and the degree-6 computation: CLASS A);
  (ii) main estimate log(q-forall) <= H_unif eps_d^-3 d^(4+eps_d) + H_K on Exc_d,
  with conditions (C1),(C2) (p.2445-2505), using Theorem 1.10: CLASS B;
  (iii) refinement with eps and eps_E <= eps: CLASS B.
* Cor 2.3 (p.3117) = Theorem A: reduces to [GenEll] Thm 2.1 (ii) using (i),(ii),(iii):
  CLASS A once (ii),(iii) are available (reduction step is formalizable).
* Section 2 begins p.2329; Prop 2.1 (p.2334) elementary estimates (log x <= x; PNT):
  CLASS A.

MAP OF THE (c) SPLIT (split point bound + unit-region bound, Cor312 Gap 2 form):
* unit-region bound <-> Theorem 1.10 holomorphic-hull log-volume estimate and its
  final display (p.1363-1385; Steps (iv)-(vi) p.1586-1680): CLASS B target.
* split point bound <-> Theorem 1.10 Step (iii) prime-splitting/rounding estimates
  (R1)-(R3) (p.1523-1545) + weighted averages p.1710-1783: CLASS B target.
* the comparisons/corrections around them (Prop 1.4 height algebra, Cor 2.2 (i),
  Cor 2.3 reduction via [GenEll] Thm 2.1): CLASS A, formalizable now.

CONCLUSION: no vague GenEll-strength wording. [GenEll] Thm 2.1 is a proved
reduction; the (c) inequality itself is the IUT-side Theorem 1.10 shape (CLASS B
formalization target), while the BD-class/height computations around it are
CLASS A.

LABEL: source classification table (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136RegionEstimateSourceClassificationActual

structure LGPRegionEstimateSourceRow where
  component : String
  exactSource : String
  /-- classA = elementary formalizable now; classB = proved in paper, formalization target -/
  sourceClass : String
  note : String

def lgpRegionEstimateSourceClassification : List LGPRegionEstimateSourceRow :=
  [ ⟨"elementary log/Pnt bounds", "IUT IV Prop 2.1 (p.2334-2378)", "classA", "log x <= x, prime number theorem bounds"⟩,
    ⟨"BD-class height equalities (1/6 log q ~ ht_inf ~ ht_omega)", "IUT IV Cor 2.2 (i) (p.2404-2428; proof p.2506-2529)", "classA", "uses [GenEll] Prop 1.4 (i),(iii) and degree-6 computation"⟩,
    ⟨"main log(q) estimate on Exc_d", "IUT IV Cor 2.2 (ii) (p.2426-2444) + (C1),(C2) (p.2475-2493)", "classB", "invokes Theorem 1.10"⟩,
    ⟨"epsilon refinement (eps_E <= eps)", "IUT IV Cor 2.2 (iii) (p.2494-2505)", "classB", "same Theorem 1.10 input"⟩,
    ⟨"undilated region/log-volume estimate (unit-region bound)", "IUT IV Theorem 1.10 final display (p.1363-1385) and Steps (iv)-(vi) (p.1586-1680)", "classB", "IUT-side; this is the (c) unit-region bound shape"⟩,
    ⟨"prime-splitting/rounding estimates (split point bound)", "IUT IV Theorem 1.10 Steps (iii)-(v): (R1)-(R3) (p.1523-1545), weighted averages (p.1710-1783)", "classB", "this is the (c) split point bound shape"⟩,
    ⟨"height/log-different/log-conductor comparison", "IUT IV Prop 1.4-1.7 (p.400-1060); [GenEll] Prop 1.4/1.6/1.7", "classB", "analytic/archimedean and log-shell estimates used by Theorem 1.10"⟩,
    ⟨"reduction to general hyperbolic curves (endpoint)", "IUT IV Cor 2.3 / Theorem A (p.3117-3155; p.93-105) via [GenEll] Thm 2.1 (p.615) equivalence", "classA", "reduction step formalizable once Cor 2.2 (ii),(iii) are available"⟩,
    ⟨"general-position reduction theorem", "[GenEll] Thm 2.1 (p.615): compactly bounded <=> general", "classA", "proved reduction; NOT a proof of ABC"⟩,
    ⟨"noncritical Belyi maps input", "[Mzk1] Noncritical Belyi Maps (repo text Noncritical Belyi Maps.txt)", "classA", "reduction input for (ii)=>(i); not IUT-side"⟩ ]

theorem lgpRegionEstimateSourceClassification_length :
    lgpRegionEstimateSourceClassification.length = 10 := rfl

def lgpRegionEstimateClassACount : Nat :=
  (lgpRegionEstimateSourceClassification.filter (fun r => r.sourceClass = "classA")).length

theorem lgpRegionEstimateClassACount_eq : lgpRegionEstimateClassACount = 5 := rfl

#check lgpRegionEstimateSourceClassification
#check lgpRegionEstimateSourceClassification_length
#check lgpRegionEstimateClassACount_eq

end LeanFormal.IUT.XiFPaper.S3136RegionEstimateSourceClassificationActual