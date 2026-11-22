# S346: orbifold structural sheaf O^tri(T_x) / O^triangleright carrier

Date: 2026-10-29. No completion root, no L, no fake carrier.

## Repo findings

Repo search found only descriptive/obligation text for O^{tri}(T_x) /
O^triangleright:

* SourcePlaceQParameterUniformization.qParameterTwoLRootDescent:
  Audit Obligation status pending; note explicitly says there is no carrier
  for the orbifold structural sheaf O^{tri}(T_x).
* SourceDefinition31D4TateQIdentification: only the q-order power kernel and
  the D4 Tate-q identification; no O^{tri} carrier.

There is no existing Lean type/definition for the orbifold structural sheaf
carrier or for a q_v^{1/2l} section in it.

## S346 exact missing spec

OrbifoldStructuralSheafCarrierSpec records the minimal required data:
* carrier : Type u with a Monoid;
* qSection, rootSection : carrier;
* qSection_toCompletion : carrier -> Completion place with
  qSection_toCompletion qSection = qVFamily.q;
* rootSection_pow : rootSection ^ (2*l) = qSection;
* structuralSheafCondition : Prop (paper O^tri condition not formalized).

OrbifoldStructuralSheafRootSectionRequired := Nonempty of the spec.  No
inhabitant is constructed; no carrier is identified with Completion or L.

## Supporting actual facts

completionCarrier_cannot_supply_root: no NatRootSystem qVUnit in the
completion (S342), so the paper root section cannot be a completion root.
sourceTorsion23Rational_available: T.clauseC.torsion23_rational is actual.

No L/transport/normalization; no fake root/carrier; no inequality.
