# S342: qVFamily completion root card is impossible

Date: 2026-10-29. Completion only; no L; no fake root.

## Repo facts used

* SourcePlaceQParameterUniformization.QParameterTwoLRootCard:
  nonzero completion root r with r^(2l) = q.
* SourceDefinition31D4TateQIdentification:
  - twoLRootCard_parameter_order_eq:
      (2*l) * card.toQCandidate.order = parameter.order;
  - twoLRootCard_l_dvd_parameter_order:
      l ∣ parameter.order;
  - twoLRootCard_parameter_order_not_coprime:
      any such card gives NOT Nat.Coprime parameter.order l.
* SourceInitialThetaData Clause B / SourceTateComparisonWitness:
  the actual qVFamily parameter has Nat.Coprime order l via its
  order_coprime field.

## Proved in S342

* qVFamilyTateWitness and qVFamily_order_coprime: actual qVFamily order is
  coprime to l.
* qVFamilyTwoLRootCard_impossible:
  no QParameterTwoLRootCard for qVFamily.
* missingKummerHenselInput_impossible:
  the S330 missing Kummer/Hensel input (same card gap) is inconsistent with
  the source order condition.
* cardOfTwoLthRootData + twoLthRootData_impossible:
  no TwoLthRootData for qVUnit in the completion.
* natRootSystem_impossible:
  no NatRootSystem (qVUnit T b) in the completion.

## Why this is stronger than a Kummer/Hensel gap

The obstruction is valuation-theoretic: a completion root of q would force
2l (hence l) to divide order(q), while clause (c) supplies
Nat.Coprime(order(q), l).  Kummer surjectivity on principal units cannot
change the order; therefore there is no Kummer/Hensel input of the current
card shape.  The paper root must live in a different carrier (orbifold
structural sheaf / root stack), not as a completion q-candidate.

No L/transport/normalization; no fake root; no inequality.
