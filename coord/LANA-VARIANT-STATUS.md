# LANA-VARIANT-STATUS — Cor312VariantHolds: definition, hypothesis status, and domain audit

Status: READ-ONLY AUDIT, 2026-11-12. No Lean file written, no compile.
Sources: Iut/Cor312/Statement.lean:80-99, Iut/Concrete/ThetaRegion.lean:345-386,
Iut/MainTheorem.lean:11-39, Iut/Tripod/Main.lean:118-133,
Iut/Cor312/LeftHandSide.lean:54-95, Iut/Cor312/RightHandSide.lean:65-109,
Iut/Cor312/ThetaData/Basic.lean:81-194, GlobalField.lean:162-184,
AdmissiblePrime.lean:106-157, Iut/Concrete/Existence.lean:62-320,
Iut/Abc/FormalConjectures.lean:240-241. No axiom/sorry in the audited files.

## 1. Definition and proof status

1. Cor312VariantData (Statement.lean:80) has exactly three fields:
   data : InitialThetaData; qPilot : QPilotData data; rhsData : RHSData data.
2. Corollary312Variant (Statement.lean:89) is a Prop-valued definition:
   X.qPilot.lhs <= X.rhsData.rhs.
   It is deliberately without proof and without axioms; the module docstring says
   no declaration in the repository proves or assumes it.
3. Cor312VariantHolds (ThetaRegion.lean:375) is a def, not a theorem:
   forall D : InitialThetaData, Corollary312Variant (concreteVariantData D).
4. concreteVariantData (ThetaRegion.lean:359) is a function of D:
   data := D; qPilot := D.qPilot; rhsData := D.rhsData.
   D.qPilot is ThetaRegion.lean:348 (badFinset from D.bad_finite; weight =
   inertDeg D.F w / finrank Q D.F); D.rhsData is the concrete theta-pilot data.
5. Cor312LiteralHolds (ThetaRegion.lean:383) is the analogous def with
   concreteVariantDataLit (rhsDataLit, all labels); cor312Literal_of_variant
   (Literal.lean:115) proves only the implication variant -> literal.

Grep for a theorem/lemma proving Cor312VariantHolds finds only:
  - def Cor312VariantHolds;
  - implication consumers (cor312Literal_of_variant, abc_of_variant,
    classicalABC_of_variant, formalConjecturesABC_of_variant,
    cor312VariantHolds_of_wall).
There is no declaration theorem Cor312VariantHolds and no instance. Therefore
Cor312VariantHolds is an UNPROVED HYPOTHESIS, not a lana theorem. It is not an
axiom either: it is a plain def, and the only way to use it is as an argument.

## 2. ABC bridge is a pure implication

MainTheorem.lean:36:
  theorem classicalABC_of_variant (h312 : Cor312VariantHolds) : ClassicalABC
The proof goes through Tripod.abc_of_variant (Tripod/Main.lean:120), which takes
h312 as an argument; no proof of h312 is supplied. Likewise:
  classicalABC_of_ss (WallEquiv/Basic.lean:180) takes forall D, SSIneq D;
  cor312VariantHolds_of_wall (Wall/EtaAlg.lean:212) takes a wall family.
All are conditional implications. The status of the input is:
  variant = hypothesis; SS/wall = hypothesis; no IUTProven/unknown flag exists.
The formalization is honest about this in MainTheorem's docstring and in
Statement.lean's no-proof-no-axiom paragraph.

## 3. Hidden qOrder/height/bound audit

Fields that could hide a bound:
- InitialThetaData (ThetaData/Basic.lean:81):
    F, Fbar, E, VBad, global : IsInitialThetaGlobalData, prime : AdmissiblePrimeData,
    orb : OrbicurveData, localData : LocalThetaData.
- IsInitialThetaGlobalData (GlobalField.lean:166):
    sqrt_neg_one; stable_reduction at every finite place; six_torsion_rational;
    bad_nonempty; bad_odd; bad_multiplicative.
  No height, conductor, discriminant, level, qOrder, or degree bound.
- AdmissiblePrimeData (AdmissiblePrime.lean:111):
    prime ell, ell>=5, mod-ell basis/rep, SL2 image, open kernel,
    galois_deg_prime, residueChar_coprime, q_order_coprime.
  No qOrder upper bound; only positive/coprime conditions. No conductor relation.
- QPilotData (LeftHandSide.lean:58):
    badFinset, badFinset_spec, weight, weight_pos.
  No height/norm bound on qOrder; logQ uses raw D.qOrder.
- RHSData (RightHandSide.lean:65):
    container, proc_standard, toRational, vol, hull, thetaPilot,
    thetaPilot_hullAdmissible.
  The container/proc/vol/hull/thetaPilot are arbitrary data fields; no qOrder or
  height bound.
- Concrete construction EllipticCurveData.thetaData (Existence.lean:303):
    conditional on CurveArithmetic, TateInputs, ModEllRepData, hP2, hP5, hcore.
    CurveArithmetic has stable reduction, six torsion rational, Galois degree prime,
    bad finiteness, inertDeg positivity, sum_inertDeg_le; no height/qOrder bound.
    hP2 is not ell divides TI.qOrder (coprimality), not an upper bound.
Conclusion: NO hidden qOrder/height/conductor/level bound in Cor312VariantHolds
or concreteVariantData. The quantifier literally ranges over every inhabited
InitialThetaData; nothing in the fields caps qOrder.

## 4. Are large-n I_n curves in the domain?

A semistable curve of type I_n has qOrder = n at its bad place (QORDER-NORMALIZATION,
QORDER-BOUND). It is NOT automatically an InitialThetaData:
- it must have stable reduction and full 2- and 3-torsion rational over F
  (six_torsion_rational), contain sqrt(-1), have bad places of odd residue
  characteristic, and satisfy the mod-ell SL2/coprimality conditions;
- over F = Q a given I_n curve usually fails six-torsion rationality, so it does
  not qualify as-is; one may try a finite extension F containing E[6] and sqrt(-1).
Whether such an F can be chosen while preserving all fields is a separate
arithmetic question; no construction in the repository proves it for all I_n.
But the formal domain has NO bound that would exclude large n in principle:
  - qOrder enters only through QPilotData.logQ (raw order);
  - the only qOrder conditions are positivity and ell-coprimality;
  - there is no height/conductor/level cap.
Therefore the I_n large-n alarm cannot be dismissed by saying the quantifier
domain contains a bound: no such bound is present.

Important consistency caveat (open, not a decisive conclusion):
qrootOf (Concrete/ThetaLocalConstruct/Data.lean:280-291) chooses a 2ell-th root
of the Tate q in the completion. An element of a discretely valued completion
has integer valuation, so 2ell (times the local ramification) divides the order
of q; this appears to conflict with AdmissiblePrimeData.q_order_coprime
(ell not dividing qOrder). Resolving this requires checking whether
TateFamily.S.t.q is the same q as tateParam q (uniqueness says it should be) or
whether the Tate family is normalized differently. Until that is clarified,
satisfiability of InitialThetaData (and hence whether Cor312VariantHolds is
vacuous) is OPEN. This does not change the proof status: the variant is still an
unproved hypothesis. It does mean "I_n belongs" and "domain empty" are both
unresolved without the qroot/TateFamily normalization audit.

## 5. Is the variant satisfiable?

- Syntactically Cor312VariantData is a structure; an inhabitant requires an
  inhabitant of InitialThetaData, QPilotData, and RHSData.
- No concrete InitialThetaData is constructed in the audited files; thetaData
  (Existence.lean:303) is conditional on EllipticCurveData + CurveArithmetic +
  TateInputs + ModEllRepData + hP2/hP5/hcore, and no actual elliptic curve with
  all these non-data facts is provided.
- S1487 (our project) is a SourceDefinition31Data scalar calibration, not an
  InitialThetaData or Cor312VariantData; it cannot instantiate the variant.
- ConcreteData in the lana tree: there is no such named structure; the concrete
  construction is concreteVariantData (a function of D) and EllipticCurveData.thetaData
  (conditional). Neither fixes/reduces qOrder.
- If InitialThetaData is empty, Cor312VariantHolds is vacuously true; if inhabited,
  no bound on qOrder. In neither case does lana prove the variant or ABC.

## 6. Verdict

1. Cor312VariantHolds is a DEFINITION/HYPOTHESIS, not a proved theorem; no axiom
   is used to assert it; classicalABC_of_variant is a pure implication.
2. The ABC bridge is conditional; it does not establish ABC unconditionally.
3. No hidden qOrder/height/conductor bound. The domain quantifies over all
   InitialThetaData; only positivity/coprimality and the Definition 3.1 arithmetic
   conditions appear.
4. Large-n I_n curves are not automatically in the domain because of the full
   2/3-torsion and mod-ell conditions, but nothing in the formal fields bounds n;
   the qroot-vs-coprime consistency caveat is an open satisfiability issue.
5. Whether the variant is true/satisfiable is OPEN; the formal status is
   HYPOTHESIS/UNPROVED.

## 7. AUDIT-LEDGER / FINAL-STATUS

AUDIT_LEDGER.md has no entry for Cor312VariantHolds status or this domain audit
(grep shows only unrelated Cor312 StepXI assembly references). FINAL-STATUS.md
gets a pointer appended after this file.
