# LANA-PAPER-DIFF — Cor 3.12 original vs lana formalization

Status: READ-ONLY comparison, 2026-11-12. No Lean file, no compile.
Paper text: coord/IUT-TEXT-COR312.md, coord/IUT-TEXT-THM110.md.
Lana: Iut/Cor312/Statement.lean; Iut/Cor312/LeftHandSide.lean;
Iut/Cor312/RightHandSide.lean; Iut/Concrete/ThetaRegion.lean;
Iut/Concrete/Literal.lean; Iut/WallEquiv/Gap.lean.

## 1. LHS: original vs lana

Original (IUT III Cor 3.12, IUT IV Thm 1.10 p.23):
  -|log(q)| = -(1/(2l)) * log(q),
  log(q) = arithmetic degree of the q-divisor (weighted q-parameters at bad
  places; weights from arithmetic degree).

Lana:
  QPilotData.logQ (LeftHandSide.lean:81-84)
    = sum_{w in badFinset} weight w * D.qOrder w * log residueChar w;
  QPilotData.absLogQ (:88) = logQ / (2 * D.l);
  QPilotData.lhs (:93) = -absLogQ.
The badFinset enumerates badPlacesOver; weight in concrete qPilot is
inertDeg D.F w / finrank Q D.F (ThetaRegion.lean:348-352).

Match: the 1/(2l) normalization and the sign are exactly the paper convention
(matching IUT-TEXT-THM110 section 1). No discrepancy in this item.

## 2. RHS: original vs lana

Original:
  -|log(Theta)| is the procession-normalized mono-analytic log-volume of the
  holomorphic hull of the union of the possible images of a Theta-pilot object,
  subject to (Ind1), (Ind2), (Ind3), in the multiradial representation of
  Theorem 3.11. Values are in R union {+infinity}.

Lana:
  RHSData.rhs (RightHandSide.lean:107)
    = R.vol.processionVol R.thetaHull,
  RHSData.thetaHull (:99) = R.hull.hullFamily R.thetaPilot,
  RHSData.thetaPilot is an explicit input field, with
  thetaPilot_hullAdmissible as a hypothesis; the whole container/vol/hull/
  thetaPilot package is input data.

Differences:
(a) Lana RHS is real-valued (RHSData.rhs : Real); the paper allows
    -|log(Theta)| = +infinity and then proves finiteness under the assumptions.
    Lana rules this out by the admissible-region/finite-volume fields, not by
    reproducing the paper's finiteness argument.
(b) Lana's thetaPilot is an INPUT. It is not the output of the multiradial
    algorithm of Theorem 3.11. There is no theorem in lana identifying
    R.thetaPilot with the possible images of the paper's Theta-pilot object
    under Ind1/2/3. This is explicitly stated in Statement.lean's honesty
    paragraph and in RHSData's module docstring.
(c) Lana's hull is an abstract ContainerHullSystem (RHSData.hull), not
    constructed as the paper's holomorphic hull; the concrete instance is a
    particular hull system. No theorem proves the paper's hull equals it.

Therefore the RHS is a formal interface matching the paper's shape, not a
formalization of the paper's multiradial construction.

## 3. The variant inequality and the C_Theta formulation

Original (Cor 3.12):
  -|log(Theta)| >= -|log(q)|, equivalently C_Theta >= -1 for real C_Theta with
  -|log(Theta)| <= C_Theta * |log(q)|.

Lana (Statement.lean:89):
  Corollary312Variant X : Prop := X.qPilot.lhs <= X.rhsData.rhs,
  i.e. -|log(q)| <= -|log(Theta)|.

Match: same inequality and sign, with the paper's LHS/RHS normalization (item 1).
Difference: lana does not define C_Theta or state C_Theta >= -1; it states the
direct real inequality. The equivalence between the two presentations is not a
separate lana theorem; it is a paper-level arithmetic rearrangement.

## 4. Quantifier and reading

Original: Cor 3.12 is stated for the fixed situation of Theorem 3.11, for a
collection of initial Theta-data; the procession average is over j in F_l^x
(all nonzero labels), and the union is over the possible images under
Ind1/Ind2/Ind3.

Lana:
  Corollary312VariantData (Statement.lean:80)
    = data : InitialThetaData, qPilot : QPilotData data, rhsData : RHSData data.
  Corollary312VariantHolds (ThetaRegion.lean:375)
    = forall D : InitialThetaData, Corollary312Variant (concreteVariantData D).
  Cor312LiteralHolds (:383) = same with concreteVariantDataLit.

So lana quantifies over ALL initial Theta-data, not a fixed one. This is a
stronger uniform statement than the paper's pointwise "suppose in the situation
of Theorem 3.11" only if one reads the paper as pointwise; in any case it is a
quantifier difference to record. There is no qOrder/height/conductor/level bound
in the quantifier (see LANA-VARIANT-STATUS).

## 5. Ind1/label reading: the largest deviation

The paper's Cor 3.12 defines the RHS with the union over the possible images of
the Theta-pilot object under Ind1/Ind2/Ind3, and averages over j in F_l^x.

Lana has TWO concrete readings:
- concreteVariantData (ThetaRegion.lean:359) uses D.rhsData, whose thetaPilot
  is D.thetaPilot with ivLabels = {distinguished j} (singleton), i.e. IUT IV's
  reading, not the literal all-label union.
- concreteVariantDataLit (:367) uses rhsDataLit with litLabels = all labels,
  the literal IUT III reading.

Facts in Literal.lean:
  rhs_le_rhsLit (Literal.lean:84): D.rhsData.rhs <= D.rhsDataLit.rhs.
  cor312Literal_of_variant (:115): Cor312VariantHolds -> Cor312LiteralHolds.
The converse (literal -> IV) is exactly the step from the literal IUT III
statement to IUT IV Steps (iv)-(v); it is NOT proved in lana.

Consequence: the hypothesis used for ABC, Cor312VariantHolds, is the IV reading
with the singleton label. The paper's literal all-label union is only the
rhsDataLit object. The two are different; lana proves variant_IV -> variant_lit,
not the paper literal statement as an exact hypothesis. The lana docstring says
the single-label readings agree up to Ind1, and rhsDataOn_singleton shows each
single-label reading has IUT IV's value; the literal union is larger, so
rhsData <= rhsDataLit.

## 6. j-average and the sFactor normalization

Original Step (iv)-(v):
- average over j in F_l^x (paper uses {1,...,l*=(l-1)/2} plus symmetry);
- before averaging, the q-term is -j^2/(2l) * log(q_{vQ});
- after averaging: -(l+1)/24 * log(q_{vQ}) (IUT-TEXT-THM110 section 4).

Lana:
  processionVol (LogVolume.lean:207) = (sum_i globalVol(R i)) / D.proc.length,
  D.proc.length = l* = (l-1)/2;
  capsule index i (Fin (nC D)); distinguished label j = i+1;
  sFactor(nC) = (nC+1)(2nC+1)/6 = l(l+1)/12;
  with A = logQ/(2l), sFactor * A = (l+1)/24 * logQ.
  gap_eq_rhs_add (Gap.lean:523):
    gap = rhs + sFactor(nC)*A - V(hull VC),
    hence rhs = V(hull VC) - sFactor(nC)*A + gap.

Match at the coefficient level: sFactor(nC)*A is exactly the paper's
-(l+1)/24 log(q) term after moving signs, and V(hull VC) is the container/hull
volume term. The paper's final 1/6 log(q) is not a separate lana definition; it
is the result of multiplying the Step (v) bracket by (l+1)/4 and using the
bounds. Lana keeps the coefficient as sFactor(nC) and the exact identity
gap_eq_rhs_add; it does not lose or rewrite the 1/6 structure, but it also does
not prove the paper's final Theorem 1.10 bound.

Difference: lana's average is over the half-set of capsules i=1..l*, with one
distinguished label j=i+1 per capsule, whereas the paper's text says average
over j in F_l^x. The numerical coefficient matches after the paper's symmetry
reduction, but the formal averaging object is not literally the paper's
F_l^x-average; it is the procession average over capsules.

## 7. Step (v) chain vs gap_eq_rhs_add

Paper Step (v) upper bound (per vQ, after average):
  (l+5)/4 log(d^K_vQ) - (l+1)/24 log(q_vQ) + log(s^Q_vQ) + ...
  <= (l+1)/4 { (1+4/l) log(d^K_vQ) - 1/6 log(q_vQ) + ... }.

Lana gap decomposition:
  gap = rhs + sFactor(nC)*A - V(hull VC),
  rhs = V(hull VC) - sFactor(nC)*A + gap,
  V(hull VC) is the lana hull-volume term; gap >= 0 collects the positive
  shell/Ind2/hull corrections.

Thus the lana identity is the paper's rearrangement with:
  V(hull VC) <-> the log-volume of the hull of the container,
  sFactor(nC)*A <-> (l+1)/24 log(q),
  gap <-> the positive correction from Ind2/shell/arch.
The 1/6 coefficient appears only after the paper multiplies by (l+1)/4 and
normalizes; it is not an additional input in lana. Conversely, lana does not
prove the paper's upper bound itself: the proof is the missing variant/SS input.

## 8. Specific deviations (summary)

1. Quantifier: paper fixed situation of Thm 3.11; lana Cor312VariantHolds is
   all InitialThetaData.{0}. This is a uniformity/strength difference.
2. RHS domain: paper R union {+infinity}; lana Real, with admissibility fields.
3. RHS construction: paper multiradial algorithm with Ind1/2/3; lana RHSData
   thetaPilot is an input; no identification theorem.
4. Label reading: paper literal union all labels; lana concreteVariantData uses
   ivLabels singleton (IUT IV reading); rhsDataLit is separate. Only
   variant_IV -> literal is proved, not literal -> IV.
5. j-average: paper average over j in F_l^x; lana procession average over
   nC=(l-1)/2 capsules with distinguished j=i+1. Coefficient matches
   sFactor(nC)*A=(l+1)/24 logQ, but the averaging object differs.
6. C_Theta: paper states C_Theta >= -1; lana states the direct inequality, no
   C_Theta definition/equivalence.
7. Ind3: paper converts upper semi-compatibility into an inequality from above;
   lana has no Ind3 region/algorithm; the hull system is an input.
8. Paper's Theorem 1.10 final bound 1/6 log(q) <= ... is not asserted by lana;
   lana retains gap = rhs + sF*A - V and the variant as a hypothesis.
9. Paper Step (v) uses Proposition 1.4/1.7 with Ind1/Ind2 and the average; lana
   uses its AbstractContainerHullSystem/LogVolumeData interfaces; the concrete
   instance is a model, not a proof of the paper's Step (v).

## 9. Verdict

- LHS normalization matches exactly (1/(2l), signs).
- RHS is a real-valued interface of the right shape, but not a construction of
  the paper's multiradial theta hull; thetaPilot is an explicit input.
- Corollary312Variant is the same inequality, with the paper's normalization,
  but the lana quantifier (all InitialThetaData) and reading (IV singleton vs
  paper literal all-label) differ.
- The sFactor/gap identity preserves the Step (v) coefficient structure
  (sFactor(nC)*A = (l+1)/24 logQ); the 1/6 appears only in the paper's
  subsequent normalization, not as a missing lana definition.
- The formalization is a conditional interface, not a proof of paper Cor 3.12;
  the main missing inputs are the variant/SS and the theta-hull/multiradial
  identification, not the LHS normalization.
