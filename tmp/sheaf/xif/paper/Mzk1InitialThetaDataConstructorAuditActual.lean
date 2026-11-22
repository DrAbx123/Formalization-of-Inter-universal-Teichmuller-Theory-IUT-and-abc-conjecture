/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-! # A738b hull: InitialThetaData fields, constructors, and SSIneq/NumericalWall formulas

Read-only audit of the lana IUT tree (`tmp/online/lana-agents__iut/iut-main`).
Records:
* the fields of `Iut.InitialThetaData` (`Iut/Cor312/ThetaData/Basic.lean:81`);
* the concrete constructors/instances (`ofExistence`, `EllipticCurveData.thetaData`,
  `Tripod.thetaDataOf`, `towerArithmetic_of_localFacts`, `concreteVariantData`, ...);
* the verbatim formulas of `SSIneq`, `SSIneqNoHull`, `NumericalWall`, `Wall` and its
  variants;
* an assessment whether OUR model can instantiate lana's `InitialThetaData`.

Only data tables are introduced; no assumption/axiom/named structure.  No RETRACTED
file referenced. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1InitialThetaDataConstructorAuditActual

/-- Fields of `Iut.InitialThetaData` (Basic.lean:81-113). -/
def initialThetaFieldRows : List (String × String × String) :=
  [ ("F", "Type u with Field F and NumberField F", "the number field F (Definition 3.1(a))"),
    ("Fbar", "Type u with Field Fbar, Algebra F Fbar, IsAlgClosure F Fbar", "chosen algebraic closure of F"),
    ("E", "WeierstrassCurve F with E.IsElliptic", "elliptic curve E_F/F (X_F = E_F minus 0)"),
    ("VBad", "Set (FinitePlace (fieldOfModuli F E))", "chosen nonempty bad nonarchimedean places of F_mod"),
    ("global", "IsInitialThetaGlobalData F E Fbar VBad", "global conditions of Definition 3.1(a)-(b)"),
    ("prime", "AdmissiblePrimeData F E Fbar VBad", "admissible prime l + mod-l representation data + coprimality (3.1(b)-(c))"),
    ("orb", "OrbicurveData F E Fbar VBad prime", "orbicurve data C_K, X_K, epsilon (3.1(d)/(f))"),
    ("localData", "LocalThetaData F E Fbar VBad prime orb", "valuation section V and local conditions (3.1(e)-(f))") ]

theorem initialThetaFieldRows_length : initialThetaFieldRows.length = 8 := rfl

/-- Derived fields/abbrevs of `InitialThetaData` (Basic.lean:121-206). -/
def initialThetaDerivedRows : List (String × String × String) :=
  [ ("X", "Anabelian.Orbicurve D.F", "once-punctured elliptic curve"),
    ("ell", "Nat", "the prime l"),
    ("K", "IntermediateField D.F D.Fbar", "l-torsion field (fixed field of ker rho)"),
    ("Kt", "Type u", "K as a type"),
    ("CKu", "Orbicurve Kt", "orbicurve C_K"),
    ("epsilon", "Cusp of CKu", "distinguished cusp"),
    ("V", "ValuationSection ...", "valuation section V subset V(K)"),
    ("galoisGroup", "Type u", "Gal(Fbar/F) with Krull topology"),
    ("tateParam", "FinitePlace D.F -> ... -> TateParameter (localCompletion w)", "Tate parameter q_w at bad w"),
    ("qOrder", "FinitePlace D.F -> ... -> Nat", "ord_w(q_w) = qOrderAt"),
    ("coprime_qOrder", "Nat.Coprime D.ell (D.qOrder w hw)", "Definition 3.1(c) for the derived q_w"),
    ("tate", "TateFamily D.E D.prime.torsionField D.prime.ell D.VBad", "Tate uniformizations over K_w (Definition 3.1(f))") ]

theorem initialThetaDerivedRows_length : initialThetaDerivedRows.length = 12 := rfl

/-- Constructors/instances of `InitialThetaData` and of its concrete data. -/
def constructorRows : List (String × String × String) :=
  [ ("Iut.InitialThetaData.ofExistence", "Cor312/ThetaData/Basic.lean:220", "general constructor from F, Fbar, E, VBad, global, prime, orb, sect, local_diagram_cartesian, bad_type, bad_theta_model, epsilon_graph; NOT unconditional"),
    ("Iut.EllipticCurveData.thetaData", "Concrete/Existence.lean:303", "concrete Theta-data from EllipticCurveData C, CurveArithmetic CA, TateInputs TI, prime l, h_l, 7<=l, ModEllRepData R, hsl, hP2, hP5, hcore"),
    ("Iut.Tripod.thetaDataOf / Tripod.towerArithmetic_of_towerLocalHyp", "Tripod/Tower.lean:79-88", "Theta-data of tripod points; tower arithmetic from TowerLocalHyp"),
    ("Iut.towerArithmetic_of_localFacts", "Tower/Main.lean:41", "TowerArithmetic D from TowerLocalFacts"),
    ("InitialThetaData.qPilot", "Concrete/ThetaRegion.lean:348", "concrete q-pilot data (badFinset, weights f_w/[F:Q])"),
    ("InitialThetaData.rhsData", "Concrete/ThetaRegion.lean:335", "concrete right-hand-side data (ivLabels)"),
    ("Iut.concreteVariantData", "Concrete/ThetaRegion.lean:359", "X = (D, D.qPilot, D.rhsData)"),
    ("InitialThetaData.invariants", "Concrete/Invariants.lean:262", "Theorem110Invariants (concreteVariantData D)"),
    ("TowerArithmetic.localEstimate", "Concrete/LocalEstimate.lean:474", "LocalEstimate from TA : TowerArithmetic D") ]

theorem constructorRows_length : constructorRows.length = 9 := rfl

/-- Verbatim formulas of the wall, its variants, and the numerical shadow. -/
def wallFormulaRows : List (String × String × String) :=
  [ ("SSIneq D", "(sFactor (nC D) - 1) * D.qPilot.absLogQ <= logVol D (hullOf D (vcI D))", "MultiContainer.lean:88 (Scholze-Stix inequality)"),
    ("SSIneqNoHull D", "(sFactor (nC D) - 1) * D.qPilot.absLogQ <= logVol D (vcI D)", "MultiContainer.lean:94 (no-hull wall; implies SSIneq)"),
    ("NumericalWall D", "exists U : Region D, IsAdelic D U and InHullOfImage D U and (qVal D.bpsDegrees).eta (logVol D U) = etaQ D", "Checks.lean:56 (numerical form of (9-1); iff Cor312Variant)"),
    ("Wall D A", "forall h1 h2, BPS.Iso (thetaBPS h1) (qBPS h2) -> exists iota S, etaAnab iota S = etaQ D", "EtaAlg.lean:173 (the named input)"),
    ("wall_iff_forall", "Wall D A <-> forall h1 h2, exists iota S, etaAnab iota S = etaQ D", "EtaAlg.lean:183 (Theta-link data vacuous)"),
    ("WallDistinct D A", "forall h1 h2, h1 != h2 -> forall gl, exists iota S, etaAnab iota S = etaQ D", "Constraints.lean:222 ((C5))"),
    ("WallOn L", "forall h1 h2, L h1 h2 -> forall gl, exists iota S, vol h2 (transport h1 h2 (out iota S)) = vol h2 (qRegionAt h2)", "MultiContainer.lean:295"),
    ("Wall3", "WallOn (fun _ _ => True)", "MultiContainer.lean:301"),
    ("WallDistinct3", "WallOn (fun h1 h2 => h1 != h2)", "MultiConstraints.lean:142"),
    ("SHEq A", "forall h1 h2, exists iota S, Rss.mk D (out iota S) (realisation ...).1 = Rss.mk D (qRegion D) (isAdelic_qRegion D)", "Constraints.lean:132; equivalent to Wall (Constraints.lean:137)") ]

theorem wallFormulaRows_length : wallFormulaRows.length = 10 := rfl

/-- Assessment: can OUR model instantiate lana's `InitialThetaData`? -/
def ourModelAssessmentRows : List (String × String × String) :=
  [ ("our native data", "LeanFormal.IUT.IUTI.InitialTheta.SourceNativeInitialThetaData (arithmetic/tuple/clauses A-F)", "different carrier; no map to lana InitialThetaData"),
    ("required F/Fbar/E/VBad", "number field F, algebraic closure Fbar, WeierstrassCurve E + IsElliptic, VBad subset of places of fieldOfModuli F E", "absent as lana structures in our repo"),
    ("required global/prime/orb/localData", "IsInitialThetaGlobalData, AdmissiblePrimeData (mod-l rep, torsion basis, q order coprimality), OrbicurveData, LocalThetaData (valuation section/tate X,C)", "absent; these are the IUT I Definitions 3.1(a)-(f) formalization"),
    ("concrete constructor inputs", "EllipticCurveData + CurveArithmetic + TateInputs + ModEllRepData + hcore + hP2/hP5", "absent in our repo; would need substantial new development"),
    ("what our repo supplies", "finite places, native place selection, root-extension/product Haar, theta/sheaf log-volumes, corrected Gap1/2, inverse scaling, B1, badPart", "partial analytic/measure inputs only"),
    ("verdict", "NO direct instantiation of Iut.InitialThetaData (nor of EtaAlg/Wall) from our model", "a bridge would require re-formalizing IUT I Def 3.1 + elliptic curve/Tate/mod-l/orbicurve core data; not currently available"),
    ("consequence", "Wall/NumericalWall/SSIneq remain NAMED inputs for our repo; no fake instance constructed", "INTEGRITY; ABC gate NOT passed") ]

theorem ourModelAssessmentRows_length : ourModelAssessmentRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1InitialThetaDataConstructorAuditActual.initialThetaFieldRows_length
#print axioms LeanFormal.IUT.XiFPaper.Mzk1InitialThetaDataConstructorAuditActual.constructorRows_length
#print axioms LeanFormal.IUT.XiFPaper.Mzk1InitialThetaDataConstructorAuditActual.wallFormulaRows_length

end LeanFormal.IUT.XiFPaper.Mzk1InitialThetaDataConstructorAuditActual