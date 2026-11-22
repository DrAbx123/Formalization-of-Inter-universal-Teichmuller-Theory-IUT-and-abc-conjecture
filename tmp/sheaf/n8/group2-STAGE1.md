# N8 group 2 - Stage 1: vertical log-Kummer and K1/K2 source realization/descent

Status: stage 1 only. No production Lean file was edited; no proof attempt was made.
Task: N8 group 2, distilled chapter 3 (logs/coordination/n8-distilled-03-log-k1k2-descent-20261018.md).
Repository snapshot read: D:/lean, 2026-10-22. Lean v4.32.2, Mathlib v4.32.2.

Short conclusion:

* the current SourceK1K2 chain is an abstract, conditional record chain, not a source realization;
* the concrete p-adic logarithm, its kernel, the torsion quotient and the completion comparison already exist in separate files;
* no theorem connects those concrete objects to K1VerticalBoundary / K2FrobenioidBoundary;
* the frozen K1 Kummer slot is provably label-free, so another theorem producing an inhabitant of that slot would not be progress;
* the smallest honest stage 2 statement is the kernel-descent criterion for the actual log carrier SourceLogShellDatum, not another K1 image-card lemma.

## 1. Paper objects and exact quantifiers

This section follows the distilled chapter's division (A-K). It does not claim the chapter is a verbatim quotation of IUT. Where a production file states a paper source, that source is repeated.

### 1.1 Multiplicative carrier, log, kernel, image

Paper-side object (chapter A):

* a multiplicative group H (actual units or principal units in the chosen local field);
* an additive-valued group homomorphism log : H -> L_add;
* T = ker(log), L = image(log);
* the short exact sequence 1 -> T -> H -> L -> 0.

Exact quantifiers:

* log is a homomorphism: forall x y : H, log (x*y) = log x + log y, and log 1 = 0;
* T = {h : H | log h = 0};
* L = {y | exists h : H, log h = y};
* the surjection H -> L is by definition of L, not by a theorem that log(H) is a prescribed lattice or the whole additive space;
* the quotient map is q : H -> H/T, and the induced map H/T -> L is a bijection.

The chapter's warning is essential: a finite-order zeta satisfies log zeta = 0 when the target is torsion-free, so torsion is contained in T; equality of torsion and T is a separate theorem, not a consequence of the exact sequence.

### 1.2 Actual log-shell

Paper-side object (IUT III, Definition 1.1, (i), as recorded in SourceLogShellCarrier.lean):

* p*_v = p_v for odd p_v, and p*_v = p_v^2 for even p_v;
* pre-log-shell is the image of the G_v(dagger Pi_v)-invariant submonoid under log;
* log-shell I_v is (p*_v)^{-1} times the pre-log-shell;
* the chapter B threshold v_p(x) > 1/(p-1) belongs to the common domain of log/exp; it is not a global inverse.

Exact Lean rendering in SourceLogShellCarrier.lean:

* SourceLogShellDatum (:86) carries p, hp, a field K, a commutative group Units, an invariant submonoid, and logMap : Units ->* Multiplicative K;
* preLogShell (:118) is {a | exists u in invariants, (logMap u).toAdd = a};
* logShell (:124) is {a | (pStar : K) * a in preLogShell};
* unitLayer (:129) is the full image of logMap;
* codomainKummerContained (:134) is the named condition unitLayer subset logShell.

This is a reduced carrier: logMap is a contract homomorphism, not Mathlib's p-adic log; the ind-topological structure and the G_v(dagger Pi_v)-action are reduced to an invariant submonoid; the archimedean case is not formalized (SourceLogShellCarrier.lean:43-55).

### 1.3 K1 object

Paper-side object: the K1 vertical log-Kummer boundary read by IUT III, Proposition 3.5 and Theorem 3.11(ii), with the IUT II Definition 4.9 times-mu-Kummer structure.

The current Lean object is Theorem311Source.K1VerticalBoundary (LeanFormal/IUT/IUTIII/Theorem311/SourceK1K2Construction.lean:56-79):

    structure K1VerticalBoundary
        (P : SourceLGPProcession l Label Choice)
        (Q : SourcePacketRealization P) where
      vertical : UpperSemiCorrespondence Nat Real
      vertical_monotone : forall m n, m <= n ->
        forall z, z in vertical.image m -> exists w, w in vertical.image n and z <= w
      nonarchimedeanImage : Nat -> Set Real -> Set Real
      archimedeanImage : Nat -> Set Real -> Set Real
      nonarchimedean_inclusion : forall m z S, z in S ->
        z in nonarchimedeanImage m S
      archimedean_surjection : forall m z S, z in archimedeanImage m S ->
        exists y, y in S and z <= y
      nonarchimedean_profile : forall m c,
        nonarchimedeanImage m (Q.possibleImage c) = Q.possibleImage (P.ind3 m c)
      archimedean_profile : forall m c,
        archimedeanImage m (Q.possibleImage c) = Q.possibleImage (P.ind3 m c)
      labelledKummer : forall c : Choice, LabelledKummerIso Choice Choice
      labelled_label : forall c a,
        (labelledKummer c).label ((labelledKummer c).inverse ((labelledKummer c).map a))
          = (labelledKummer c).label a

Exact quantifiers of the four image cards, as isolated in K1K2BoundaryReduction.lean:

* N1 nonarchimedeanImageInclusion (:140): forall m c, Q.possibleImage c subset Q.possibleImage (P.ind3 m c).
* N2 ind3ImageWellDefined (:168): forall m c c', Q.possibleImage c = Q.possibleImage c' -> Q.possibleImage (P.ind3 m c) = Q.possibleImage (P.ind3 m c').
* A1 archimedeanTargetLift (:194): forall m c z, z in Q.possibleImage (P.ind3 m c) -> exists y in Q.possibleImage c, z <= y.
* vertical and vertical_monotone: forall m <= n, every z in level m is bounded above by some w in level n.

The K1 constructor k1FromImageCards is at K1K2BoundaryReduction.lean:368; the exact characterization is k1VerticalBoundary_nonempty_iff at :391-405.
The canonical projection from a supplied realization is k1OfRealization at SourceK1K2Construction.lean:274-286.

### 1.4 K2 object

Paper-side object: IUT III, Proposition 3.7 and Proposition 3.10, plus Theorem 3.11(i)(c):

* local and global Frobenioid data;
* mod : X -> Y and MOD : Y -> X;
* degree and realification compatibility;
* transport compatibility;
* a comparison/evaluation square;
* the upper-semi direction shared with K1.

The current Lean object is K2FrobenioidBoundary (SourceK1K2Construction.lean:350-385). Its exact fields are:

    structure K2FrobenioidBoundary
        (R : SourceTheorem311Realization l Label Choice)
        (K : K1VerticalBoundary R.procession R.packet)
        (X : Type ux) (Y : Type uy)
        [CommMonoid X] [CommMonoid Y] where
      localFrobenioid : SourceProposition37Frobenioid X
      globalFrobenioid : SourceProposition37Frobenioid Y
      modMap : X -> Y
      MODMap : Y -> X
      mod_degree : forall x, globalFrobenioid.degree (modMap x) = localFrobenioid.degree x
      MOD_degree : forall y, localFrobenioid.degree (MODMap y) = globalFrobenioid.degree y
      mod_realification : forall x,
        globalFrobenioid.realification (modMap x) = localFrobenioid.realification x
      MOD_realification : forall y,
        localFrobenioid.realification (MODMap y) = globalFrobenioid.realification y
      mod_transport : forall x,
        modMap (localFrobenioid.transport x) = globalFrobenioid.transport (modMap x)
      MOD_transport : forall y,
        MODMap (globalFrobenioid.transport y) = localFrobenioid.transport (MODMap y)
      comparison : SourceProposition310Comparison Choice Choice
      comparison_local : comparison.localMap = R.evaluation.evaluation.localMap
      comparison_global : comparison.globalMap = R.evaluation.evaluation.globalMap
      comparison_lower : comparison.lower = R.evaluation.evaluation.localComp
      comparison_upper : comparison.upper = R.evaluation.evaluation.globalComp
      upperSemi : UpperSemiCorrespondence Nat Real
      upperSemi_eq_k1 : upperSemi = K.vertical

SourceProposition37Frobenioid (SourceDependencyChain.lean:995-1008) is a commutative monoid with:

* degree : X ->* Multiplicative Real;
* realification : X -> Real, additive over multiplication, equal to degree after coercion;
* effective : X -> Prop with effective_proved : forall x, effective x;
* transport : X -> X with degree invariance.

SourceProposition310Comparison (SourceDependencyChain.lean:1251-1267) additionally has lower_natural : forall a, lower a = a and upper_natural : forall b, upper b = b, so its displayed square is definitionally trivial after those fields.

## 2. Actual consumer

There are two disjoint consumer chains in the current tree.

### 2.1 Abstract K1/K2 consumer chain

The actual registered downstream consumer is the Theorem 3.11 assembly, not a log theorem:

1. SourceInternalWiring stores k1 : K1VerticalBoundary R.procession R.packet and k2 : K2FrobenioidBoundary R k1 X Y (SourceInternalWiring.lean:380-391).
2. SourceInternalWiring.canonical builds the same pair from a supplied K2 boundary (SourceInternalWiring.lean:405-415).
3. SourceK1K2Item2526Consumption.sourceInternalWiringOfLinkLayer supplies that K2 boundary from a PrimeStripFrobenioidLinkLayer plus four comparison alignments (SourceK1K2Item2526Consumption.lean:168-183).
4. SourceK1K2VerticalRealization provides the item-27/28 consumer-shaped constructors (SourceK1K2VerticalRealization.lean:60-71 and :116-160).
5. The Theorem 3.11 assembly consumes the K2 boundary in SourceTheorem311Assembly.canonicalCompletion (:1375-1385) and in the projection/layer chain (:1062-1070).

Thus, if a new theorem is to reduce a hypothesis of the actual Theorem 3.11 chain, it must eventually produce one of the fields of K1VerticalBoundary or K2FrobenioidBoundary.

### 2.2 Concrete analytic consumer chain

The concrete p-adic chain has its own consumers, but it does not import the K1/K2 records:

* LogSourceK1K2Consumer.sourceK1K2_logKummer_consumer_square (LogSourceK1K2Consumer.lean:76-105) bundles:
  - the principal-unit log square for all u;
  - the unscaled unit-log/K2 square for all integral units;
  - logShellScale p = if p = 2 then p^2 else p;
  - p-power scaling;
  - scaled log-shell scaling.
* PrincipalUnitTorsionConsumer consumes the actual torsion quotient logarithm and its injectivity (PrincipalUnitTorsionConsumer.lean:158-168).
* FinitePlaceSourceLogKernel.completionUnitLogTorsionQuotientHom (:39-45) and its injectivity (:52-60) are the actual descent map at a completion.
* IntegralUnitLogarithmKernel.unitLogTorsionQuotientEquivRange (:83-103) is the exact quotient-by-torsion to image equivalence for a general local field.

Consumer gap. The concrete chain proves the log square, the log-shell image identity, and the torsion quotient; the abstract chain proves conditional K1/K2 records. No file in the tree connects the two. This is the actual consumer split that a stage 2 statement must respect.

## 3. Existing Lean donors (file:line)

### 3.1 K1-side donors

* SourceVerticalRealization, SourceHodgeTheaterBridge.lean:528-553. 10-field abstract vertical record; includes kummer : forall c, LabelledKummerIso Choice Choice.
* SourceVerticalRealization.correspondence, same file :564-574. Sets D := Real, F := fun _ => Choice, log := fun n c => P.ind3 n c, kummer := fun _ c => Q.logVolume c. This is not the p-adic log.
* K1VerticalBoundary, SourceK1K2Construction.lean:56-79. The source-facing K1 record.
* k1OfRealization, SourceK1K2Construction.lean:274-286. Projects a supplied SourceTheorem311Realization.vertical to K1.
* VerticalLogKummerCorrespondence, LeanFormal/IUT/IUTII/Kummer/VerticalLogKummer.lean:17-24. D preorder, F : Nat -> Type, log : F m -> F (m+1), kummer : F m -> D, and only kummer m x <= kummer (m+1) (log m x). No group, no kernel, no image.
* LabelledKummerIso, SourceFaithfulBoundary.lean:196-202. map, inverse, two inverse laws, label : A -> Nat, one label round-trip law.
* identityLabelledKummerIso, K1K2BoundaryReduction.lean:209-215. Identity bijection, constant label 0.
* nonarchimedeanImageInclusion, K1K2BoundaryReduction.lean:140-142. N1 card.
* ind3ImageWellDefined, K1K2BoundaryReduction.lean:168-171. N2 card.
* archimedeanTargetLift, K1K2BoundaryReduction.lean:194-197. A1 card.
* k1FromImageCards, K1K2BoundaryReduction.lean:368-389. Builds K1 from N1, N2, A1 and an arbitrary kappa.
* k1VerticalBoundary_nonempty_iff, K1K2BoundaryReduction.lean:391-405. Nonempty K1 iff N1 and N2 and A1; kappa is unrestricted.
* LogShellRayPresentation, SourceK1K2Realization.lean:107-109. forall c, Q.possibleImage c = L inter Set.Ici (h c).
* k1BoundaryOfLogShellPresentation, SourceK1K2Realization.lean:159-174. K1 from ray presentation plus hind3, hunbounded, hsep, hclass and kappa.
* sourceVerticalRealizationOfLogShellPresentation, SourceK1K2VerticalRealization.lean:60-71. Item-27 conditional inhabitant of SourceVerticalRealization.
* not_logShellRayPresentation_of_two_singletonImages, SourceK1K2CardReduction.lean:168-184. A packet with two strictly ordered singleton images admits no ray presentation.

The last donor is a pruning result: the ray route is not a general source realization. The file itself records the separation at SourceK1K2CardReduction.lean:23-30 and :166-184.

### 3.2 K2-side donors

* SourceProposition37Frobenioid, SourceDependencyChain.lean:995-1008. Reduced Frobenioid value data on a CommMonoid.
* SourceProposition310Comparison, SourceDependencyChain.lean:1251-1267. Reduced comparison, with lower/upper pointwise identity fields.
* sourceProposition37FrobenioidOfValueKernel, SourceK1K2Realization.lean:223-234. Identity field bridge from FrobenioidValueKernel.
* k2FrobenioidBoundaryOfLinkLayer, SourceK1K2Realization.lean:240-271. K2 from a PrimeStripFrobenioidLinkLayer plus four comparison alignments.
* k2FrobenioidBoundary_nonempty_of_finitePlaceModel, SourceK1K2Realization.lean:277-297. Conditional finite-place K2 inhabitant; MODDirectionCard still supplied.
* k2FromFields, SourceK1K2Construction.lean:566-617. Field-by-field K2 constructor; every law is an argument.
* k2FrobenioidBoundaryOfLinkLayerOverRealization, SourceK1K2VerticalRealization.lean:116-127. The item-28 consumer-shaped K2 constructor.
* frobenioidValueKernelOfValueMap, SourceK1K2ValueMapEntry.lean:74-98. Value map plus transport invariance gives a reduced kernel.
* zeroValueMapKernel_not_rationalImage, SourceK1K2ValueMapEntry.lean:244-255. A legal K2 value kernel with image {0}, hence not the rational line.

### 3.3 Concrete log and log-shell donors

* SourceLogShellDatum, SourceLogShellCarrier.lean:86-95. Units ->* Multiplicative K plus invariants; reduced log-shell carrier.
* preLogShell, SourceLogShellCarrier.lean:118-119. Image of invariant submonoid under logMap.
* logShell, SourceLogShellCarrier.lean:124-125. (pStar)^{-1} * preLogShell.
* unitLayer, SourceLogShellCarrier.lean:129-130. Full logMap image.
* codomainKummerContained, SourceLogShellCarrier.lean:134-135. Named unitLayer subset logShell condition.
* toNonarchimedeanUpperSemi, SourceLogShellCarrier.lean:291-304. Turns the datum into NonarchimedeanLogKummerUpperSemi; kummer is (logMap u).toAdd.
* sourceLocalLogShellDatum, SourceLocalLogShellDatum.lean:47-57. Actual per-place datum over CommonPrimeCompletion place, with Units = (Integers L)^x and logMap = unitLogHom.
* sourceLocalLogShellDatum_logShell_eq_integralLogShell, SourceLocalLogShellDatum.lean:108-132. The datum's logShell is exactly the actual integralLogShell of the common-prime completion.
* MonoAnalyticLogShellCompactCarrier, MonoAnalyticLogShellCompactCarrier.lean:71. Compact topological module API with continuous contract log and scaling; no I-layer/arch content.
* MonoAnalyticLogShellMixedPacket, MonoAnalyticLogShellMixedPacket.lean:56. Q-span/multiplicative mixed slice set with named per-factor conditions.
* principalUnitLog and principalUnitLogHom, Example36LogDomainActual.lean:95-108. Actual principal-unit logarithm and its homomorphism.
* principalUnitLogKernel and principalUnitLogImage, Example36LogDomainActual.lean:111-127. Actual T and L.
* principalUnitLogQuotientEquivImage, Example36LogDomainActual.lean:129-135. Actual H/T to L by QuotientGroup.quotientKerEquivRange.
* logKummer, Example36LogKummerMap.lean:70-75. principalUnits concreteLogShellField to principalUnitLogShell, x maps to unitLog x.
* logKummer_surjective, Example36LogKummerMap.lean:86-90. Surjective onto the shell by definition of the shell.
* logKummer_mul, Example36LogKummerMap.lean:99-103. Additivity of the log map.
* logKummer_eq_zero_iff_isOfFinOrder, Example36LogKummerMap.lean:134-156. Actual kernel equals finite-order locus in this concrete case.
* logKummerData, Example36LogKummerMap.lean:231-238. Packages H, shell, log, Frobenius, p-scaling, surjectivity, commutation.
* SourceFrobeniusLogKummerIdentificationCard, Example36LogKummerMap.lean:339-363. The uninhabited source-identification card; no theorem consumes one (:332-338).
* sourceLogKummer and sourceLogShell, Example36SourceLogKummerIdentification.lean:102-114. Independent Q_l source log and shell.
* sourceLogKummer_square, Example36SourceLogKummerIdentification.lean:130-134. Frobenius/scaling square on the independent Q_l carrier.
* sourceComparison_obstruction, Example36SourceLogKummerIdentification.lean:196-204. Records that the concrete and source fields differ; Q5 is the only field-level comparison.
* concretePlace_qFiveComparisonRingEquiv, Example36SourceLogKummerIdentification.lean:263-267. Actual Q5 completion ring equivalence.
* concretePlace_principalUnitsEquiv, Example36SourceLogKummerIdentification.lean:347-369. Actual principal-unit equivalence at Q5.
* unitLogToLattice and K2Map, LogCarrierK1K2.lean:44-47 and :63-67. Actual K1 lattice map and K2 comparison map over the completion isometry.
* K1K2_naturality, LogCarrierK1K2.lean:74-81. K2Map (unitLogToLattice u) = unitLogToLattice (integralUnitMap u).
* principalUnitLog_naturality, LogKummerK1K2.lean:54-77. Actual principal-unit log square over completionIsometryEquiv.
* principalUnitLog_image_compat, LogKummerK1K2.lean:81-89. Every transported source log value lies in the target log image.
* completionLogShell_image_compat, LogKummerK1K2.lean:94-99. Target log-shell equals scaled unit-log range.
* completionUnitLogHom_ker_eq_torsion, FinitePlaceSourceLogKernel.lean:32-36. Actual completion log kernel equals torsion.
* completionUnitLogTorsionQuotientHom, FinitePlaceSourceLogKernel.lean:39-45. Actual induced logarithm on the torsion quotient.
* completionUnitLogTorsionQuotientHom_injective, FinitePlaceSourceLogKernel.lean:52-60. Actual descent map is injective.
* unitLogTorsionQuotientEquivRange, IntegralUnitLogarithmKernel.lean:83-103. Actual quotient-by-torsion to log image equivalence.

## 4. Exact gaps

### G1. log in the K1 chain is ind3, not the p-adic log

SourceVerticalRealization.correspondence (SourceHodgeTheaterBridge.lean:564-574) sets:

    D := Real
    F := fun _ => Choice
    log := fun n c => P.ind3 n c
    kummer := fun _ c => Q.logVolume c

VerticalLogKummerCorrespondence (VerticalLogKummer.lean:17-24) therefore has no group structure, no kernel, no image, no quotient, and no analytic logarithm. Its only law is monotonicity kummer m x <= kummer (m+1) (log m x).

Consequence: every theorem about VerticalLogKummerCorrespondence is a theorem about an abstract preorder-valued transport, not about log : O^x -> K.

### G2. The K1 Kummer slot is provably free, not arithmetic

SourceK1K2KummerSlotSeparation proves:

* any lab : A -> Nat yields an admissible slot labelledKummerRelabel A lab (:61-68);
* two admissible slots with the same underlying map and different labels exist (:94-100);
* the same freedom persists at the assembled K1 boundary (k1FromImageCards_labelledKummer_slot_free, :122-142);
* any constant label is admissible (k1FromImageCards_label_constant_free, :148-157).

The file's own status paragraph (:9-36) says the frozen slot has no compatibility with P.ind3 or Q.logVolume, and that the ordered-layer contract supplies only Real-valued monotone transport, hence no Choice-level Kummer bijection.

Therefore a stage 2 theorem of the form Nonempty (K1VerticalBoundary P Q), or forall c, LabelledKummerIso Choice Choice, would be inhabited by identityLabelledKummerIso and would not represent the paper's times-mu-Kummer structure. This is a hard interface gap, not a missing tactic.

### G3. K1 has no H, T, L, quotient, or descent

The K1 record's carrier is the abstract index type Choice. It has:

* no multiplicative group structure;
* no map Choice -> some additive L;
* no kernel subgroup;
* no quotient Choice/T;
* no theorem that a K1 image function is constant on log fibers.

The concrete exact sequence exists elsewhere (IntegralUnitLogarithmKernel.unitLogTorsionQuotientEquivRange, FinitePlaceSourceLogKernel.completionUnitLogTorsionQuotientHom), but it is not imported by SourceK1K2Construction, SourceK1K2Realization, or SourceK1K2VerticalRealization.

### G4. No action descent and no section/cocycle

Chapter D-F requires:

* an action A -> Aut(H) and rho : A -> Aut(L) with log(a*h) = rho(a)(log h);
* stability of T;
* the induced action on H/T;
* a section defect c(y,z) = s(y)s(z)s(y+z)^{-1} in T and its cocycle identity;
* an equivariance defect eta(a,y) = (a*s(y))*s(rho(a)y)^{-1} in T;
* separate treatment of two actions, with only quotient-level commutation if that is what the consumer needs.

None of these appears in K1VerticalBoundary, K2FrobenioidBoundary, or VerticalLogKummerCorrespondence.

SourceLogShellActionCompatibility has an action structure, but it acts on the log-coordinate fields (D i).K by Q-linear automorphisms (:87-96), with compatibility stated for a supplied chain S; it does not act on D.Units and does not prove log(a*h) = rho(a)(log h). Its log-volume compatibility (:204-212) is gate data, not a constructed p-adic volume.

### G5. SourceLogShellDatum is a contract, not the actual log

SourceLogShellCarrier.lean:43-55 explicitly lists the reductions:

1. the ind-topological field is reduced to its log-coordinate field K;
2. the G_v(dagger Pi_v) action is reduced to an invariant submonoid;
3. Mathlib has no p-adic log, so logMap is an arbitrary contract homomorphism;
4. codomainKummerContained is a named condition, not proved;
5. the archimedean case is not formalized.

Thus for an arbitrary D, D.logMap.ker is not known to be torsion and D.logShell is not known to be the paper's I_v. The per-place instantiation sourceLocalLogShellDatum supplies the actual log-shell identity (SourceLocalLogShellDatum.lean:108-132), but it still carries no K1/K2 bridge.

### G6. No bridge from concrete completion data to K1/K2

The concrete donors cover:

* an actual per-place SourceLogShellDatum over CommonPrimeCompletion place (SourceLocalLogShellDatum.lean:47-57), whose logShell is exactly the actual integralLogShell (:108-132);
* actual Q_l and Q5 log maps (Example36LogKummerMap, Example36SourceLogKummerIdentification);
* actual all-finite-place principal-unit log squares (LogKummerK1K2, LogSourceK1K2Consumer);
* actual K2 lattice map (LogCarrierK1K2.K2Map);
* actual torsion quotient (FinitePlaceSourceLogKernel).

The abstract donors cover:

* K1 image cards (K1K2BoundaryReduction);
* conditional K1/K2 assembly (SourceK1K2Realization, SourceK1K2VerticalRealization);
* reduced Frobenioid value kernels (PrimeStripsFrobenioidLinks, SourceK1K2ValueMapEntry).

No declaration has a type containing both a concrete carrier (for example SourceCompletion place) and K1VerticalBoundary or K2FrobenioidBoundary. This is the central N8 group-2 gap.

### G7. K2 is a reduced value record, not a Frobenioid construction

SourceProposition37Frobenioid (SourceDependencyChain.lean:995-1008) is a CommMonoid plus a degree hom, an additive realification, a unit, an effective predicate required for every element, and an arbitrary transport with degree invariance.

It does not contain:

* a Frobenioid category or its morphisms;
* a local/global construction of the Frobenioid;
* the finite-support / almost-everywhere-unit condition;
* the tensor-power/divisor dictionary of chapter G-H;
* an inverse law for mod/MOD.

frobenioidValueKernelOfValueMap (SourceK1K2ValueMapEntry.lean:74-98) constructs the record from an arbitrary value map; zeroValueMapKernel_not_rationalImage (:244-255) proves the record does not constrain the image.

### G8. K2 mod/MOD are not natural isomorphisms

K2FrobenioidBoundary (SourceK1K2Construction.lean:350-385) has:

* modMap : X -> Y, MODMap : Y -> X;
* pointwise degree/realification/transport equations;
* no MODMap after modMap equals id, no modMap after MODMap equals id;
* no monoid-hom law for either map;
* no naturality square against Frobenioid morphisms.

SourceProposition310Comparison has lower_natural and upper_natural as pointwise identity fields (SourceDependencyChain.lean:1266-1267), so comparison.square reduces to localMap a = localMap a (:1304-1306). This is a reduced comparison, not the paper's evaluation isomorphism.

### G9. Global degree / MOD/mod and finite support are absent

Chapter H and J require the local integral structures and the global rational functions/divisors to be tied by one global one-dimensional F-space and the product formula. The current K2 record:

* has no finite-support condition;
* has no global degree formula;
* has no relation between the local value maps and the global degree;
* allows modMap/MODMap to be arbitrary functions satisfying only the listed equations.

The finite-place self-link model in PrimeStripsFrobenioidLinks supplies a reduced global carrier, but MODDirectionCard remains a named missing arithmetic direction; see SourceK1K2ValueMapEntry.lean:31-47 and PrimeStrips.lean:12.

### G10. The archimedean object is absent

K1VerticalBoundary.archimedeanImage is an arbitrary Nat -> Set Real -> Set Real with two laws. There is no Psi-cns, no Psi-log orbit, no radius/closed-ball carrier, and no relation to the archimedean log of chapter I. The concrete Q5 work is nonarchimedean.

### G11. The ray presentation is false in general

not_logShellRayPresentation_of_two_singletonImages (SourceK1K2CardReduction.lean:168-184) proves: if Q.possibleImage c = {v}, Q.possibleImage c' = {v'} and v < v', then there is no L, h with LogShellRayPresentation Q L h.

This is a decisive pruning result:

* the ray route possibleImage c = L inter [h c, infinity) cannot be assumed for a general packet;
* hpres is not a harmless interface hypothesis;
* the correct next object must keep the actual log image/descent, not force a ray shape.

The file's own summary (SourceK1K2CardReduction.lean:23-30) says the K1 route still needs the ray law; the present stage 1 reads that as a reason to change route, not to prove the impossible law.

### G12. hclass is only reduced to a volume-translation law

hclass_negLogVolume_iff (SourceK1K2CardReduction.lean:111-121) reduces the canonical height condition to a volume-class law. hclass_translation_of_shift (:123-130) gives a sufficient condition: a shift : Nat -> Real with Q.logVolume (P.ind3 m c) = Q.logVolume c + shift m.

That shift is not constructed for the actual source. The finite model proves it only for normalizedLogVolume on ProcessionChoice (:194-207). This is a conditional gap, not source content.

### G13. Mono-analytic carrier exists only as a reduced API and is not connected

MonoAnalyticLogShellCompactCarrier (IUTII/Kummer/MonoAnalyticLogShellCompactCarrier.lean:71) supplies a compact Hausdorff topological Z-module carrier, a compact topological unit group, a closed invariant submonoid, a continuous contract logMap and a continuous additive scaling. Its own boundary (:45-54) says it does not prove the I-layer inclusion, does not construct the mixed packet, and does not contain the arch Psi-cns carrier or the Psi-log orbit/surjection.

MonoAnalyticLogShellMixedPacket (IUTII/Kummer/MonoAnalyticLogShellMixedPacket.lean:56) supplies a mixed slice set only in a Q-span/multiplicative reduced model, under named per-factor and unit-membership conditions (:30-44).

No theorem connects either carrier to K1VerticalBoundary.possibleImage, K1VerticalBoundary.vertical, or K2FrobenioidBoundary. This is the mono-analytic part of the group-2 gap named in the master stage1 record.

## 5. Smallest stage 2 statement

### 5.1 Why not a K1 theorem

A theorem producing K1VerticalBoundary would need either:

* the six ray/presentation hypotheses, which include the false-in-general hpres; or
* the N1/N2/A1 cards plus a kappa family, where kappa is free and N1/N2/A1 are exactly the reduced image cards already isolated.

Neither reduces the actual missing premise: an actual multiplicative carrier, log, kernel, quotient, and source Kummer structure. Adding another constructor in this interface would be record assembly, not source realization.

A theorem producing K2FrobenioidBoundary would likewise add another constructor whose modMap, MODMap, and comparison are supplied, not constructed.

### 5.2 The chosen statement

The coordinator's master stage1 names the group-level target sourceVerticalLogKummer_realization with actual inputs l, v, F_v and E_F. That name has no current declaration and no precise type in the frozen K1 interface: l, v, F_v and E_F are source objects that K1VerticalBoundary does not carry. Writing it as a free structure with those fields would violate the SHEAF rule against manufacturing objects as free fields. The smallest statable theorem-level subnode is therefore the descent criterion for the actual log carrier SourceLogShellDatum. It is the exact content of chapter C and is a prerequisite for any non-vacuous K1 Kummer slot. The parent node sourceVerticalLogKummer_realization should be stated only after the actual K1 carrier is fixed; see 5.4 and the decision log.

Proposed declaration (new file under tmp/sheaf/n8/, not production):

    import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
    import Mathlib.GroupTheory.QuotientGroup.Basic

    namespace LeanFormal.IUT

    universe u

    theorem SourceLogShellDatum.descends_iff
        (D : SourceLogShellDatum) {Y : Type u}
        (f : D.Units → Y) :
        (∃ fbar : D.logMap.range → Y,
          ∀ u : D.Units,
            fbar ⟨D.logMap u, ⟨u, rfl⟩⟩ = f u) ↔
        (∀ (u t : D.Units), t ∈ D.logMap.ker → f (t * u) = f u) := by
      sorry

    end LeanFormal.IUT

The precise type is:

    (D : SourceLogShellDatum) → {Y : Type u} → (D.Units → Y) →
      ((∃ fbar : D.logMap.range → Y,
          ∀ u : D.Units,
            fbar ⟨D.logMap u, ⟨u, rfl⟩⟩ = f u) ↔
        (∀ (u t : D.Units), t ∈ D.logMap.ker → f (t * u) = f u))

Notes on the type:

* D.logMap : D.Units ->* Multiplicative D.K; hence D.logMap.ker is a subgroup and D.logMap.range is a subgroup of Multiplicative D.K.
* ⟨D.logMap u, ⟨u, rfl⟩⟩ is the range element represented by u.
* D.Units is a CommGroup, so the left multiplication t * u is the chapter's t h; no noncommutative side condition is hidden.
* The forward direction is fbar well-definedness; the reverse direction is the quotient descent.
* The theorem does not claim D.logMap.ker = torsion; that is a separate source fact (proved for the concrete completion in FinitePlaceSourceLogKernel.lean:32-36, not for an arbitrary SourceLogShellDatum).
* The theorem does not claim that f is a K1 image map; it is the universal criterion that a future K1 constructor must satisfy.

A one-line donor for the proof is Mathlib's QuotientGroup.quotientKerEquivRange D.logMap, already used at Example36LogDomainActual.lean:129-135 and IntegralUnitLogarithmKernel.lean:83-103. The stage 2 file may state the theorem with the above sorry; statement_compiles is the only acceptance claimed at this stage.

### 5.3 What this statement does and does not close

Closes:

* the missing named quotient H/T and the exact factorization H -> H/T to L at the level of the generic source log carrier;
* the exact chapter C criterion, in a form reusable by a K1 constructor that carries actual D.Units and D.logMap instead of the abstract Choice index;
* a non-vacuous prerequisite for the Kummer slot: the slot can be built on L only after such a descent is available.

Does not close:

* the identification of D.logMap with the actual p-adic log at a place (G5-G6);
* the K1 image cards N1/N2/A1 on an actual carrier (G3);
* the times-mu-Kummer/root-system structure and its labels (G2);
* the action equivariance and section cocycle (G4);
* K2 Frobenioid, MOD/mod naturality, global degree, or archimedean objects (G7-G10).

### 5.4 Actual consumer status of this statement

There is no existing declaration whose type consumes SourceLogShellDatum.descends_iff. The nearest existing consumers are:

* SourceLogShellDatum.toNonarchimedeanUpperSemi (SourceLogShellCarrier.lean:291-304), which reads kummer := fun _ u => (D.logMap u).toAdd; a future refactor must replace this read by the quotient descent;
* SourceInternalWiring.k2 and SourceTheorem311Completion (SourceInternalWiring.lean:389-391, SourceTheorem311Assembly.lean:1375-1385), which consume only the abstract K1/K2 records and therefore cannot consume the descent lemma until a K1 constructor is changed.

This absence is the finding, not a defect of the statement. The alternative - claiming that identityLabelledKummerIso or a ray-presentation constructor is the source realization - is explicitly excluded by G2 and G11.

## 6. Stage and acceptance record

| Metric | Value |
|---|---|
| statement_compiles | not run for the proposed stage 2 file (stage 1 only) |
| proof_body_checked | not applicable |
| kernel_closed | no |
| target_accepted | no |
| Production edits | none |
| New Lean files | none |
| New sorry | none in this stage 1 file |

Current interface versions read (SHA256, uppercase):

| File | SHA256 |
|---|---|
| SourceK1K2Construction.lean | 05DA83BC1AB91D9D3B01CE76882EE967C653DD4EC5ED91ADF5736DF2429A2DC3 |
| SourceK1K2Realization.lean | 0F8ACA41D5133FC13D017068D4A4F5B76F6C56B004FBA72CCFD6E0991A782C95 |
| SourceK1K2VerticalRealization.lean | 169CA573E30938139759CAF930DFCEAF935C69A71A64C12423042AF12B130CBB |
| VerticalLogKummer.lean | D50DEDBCCE48B57FD59BB744DDEB5953A68FA3A25A237D694E1663444A0F55C3 |
| K1K2BoundaryReduction.lean | 2D19720D8DAB672BC84AAE24727EE8CCEF0E82D39E11C439DE1871435BF1D2DD |
| SourceLogShellCarrier.lean | 4A5414EA0704F6BAF860A7331F8A53E03931684F3452D902C7DA01647234113B |
| SourceLocalLogShellDatum.lean | 807EA230C4F11833B0C3FF07A44B393E8B76C5A6AC38968BF3E7F90F5233A5E2 |
| MonoAnalyticLogShellCompactCarrier.lean | E44FC834D08DDD6FF335D20DED742EC5BCBB832113289EFB1D62B0140913AC0D |
| MonoAnalyticLogShellMixedPacket.lean | C58C208DF92F9888F73065BED4E63E98C85007103231600B34ADC736516630CA |
| Example36LogKummerMap.lean | F3A4FA46EACFB54035EE46E6DA36A7D03153347A653CFFC6C15884E9B48F030B |
| LogCarrierK1K2.lean | 5F3A779391CB4048F51E6C08E9C7F3A1F3303939A031C81451103D0A91552FF7 |
| FinitePlaceSourceLogKernel.lean | 2B3C52782E750BE07DB4335D2934D315DC0657590BF715F56EF95F48B6C70EA9 |

## 7. One next action

Create tmp/sheaf/n8/LogDescentStatement.lean with the declaration in 5.2 (same imports, namespace, and sorry), then compile it once with:

    pwsh -NoProfile -File tools/build_guard.ps1 -Command 'lake env lean tmp/sheaf/n8/LogDescentStatement.lean' -WorkDir 'D:/lean' -WaitTimeoutSec 60

Record the exit status as statement_compiles; do not call it proof_body_checked or kernel_closed.

## 8. Decision log for the next worker

1. Do not extend the K1 ray route: hpres is refuted for a two-singleton packet (SourceK1K2CardReduction.lean:168-184).
2. Do not use identityLabelledKummerIso as source Kummer data: the slot is label-free (SourceK1K2KummerSlotSeparation.lean:122-157).
3. Reuse the concrete log/quotient donors (Example36LogDomainActual.lean:129-135, FinitePlaceSourceLogKernel.lean:32-60, IntegralUnitLogarithmKernel.lean:83-103) rather than reproving H/T to L.
4. The next node after 5.2 should be an actual K1 carrier whose Choice is replaced by a genuine multiplicative/log carrier. That is a target/interface decision, not a proof of the frozen record.
5. K2 should be approached through LogCarrierK1K2.K2Map and the completion isometry only after the K1 carrier question is settled; otherwise a new K2 record will again have a free modMap and a free comparison.
