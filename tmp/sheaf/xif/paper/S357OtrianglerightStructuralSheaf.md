# S357: O^tri structural sheaf candidate carrier / exact missing definition

Date: 2026-10-29. No completion root, no L, no fake carrier.

## Paper description read

Repo wiki text for IUT I Example 3.2(iv), cross-checked with
SourcePlaceQParameterUniformization and SourceDefinition31D4TateQIdentification:

* q_v admits a 2l-th root in O^triangleright(TX_v);
* Theta_v(-q_v) = q_v^(1/2l), up to mu_2l;
* q_v^(1/2l) defines N * log_Phi(q_v), the q-normalized split Frobenioid
  C_v^tri;
* the object is an orbifold structural sheaf/root-stack object, not a
  completion element and not an L/root-extension element.

## Existing repo structures that can carry it

* Iut.PreFrobenioid.LinearBaseIdentityEndomorphism A:
  actual object monoid O^triangle(A) (Frobenioids I, Proposition 2.2).
* Units of that monoid: O^times(A).
* Iut.PreFrobenioid.CharacteristicSplitting.tau:
  characteristic submonoid tau(A), with the splitting
  O^times(A) x tau(A) ~= O^triangle(A).
* Iut.SplitFrobenioidPresentation:
  actual packaged split Frobenioid (Examples 3.2-3.4), with rational monoid
  transport, splitting index and characteristic splittings.

Missing pieces:

1. a definition of the paper's O^triangleright(T_x) as a positive/log-shell
   submonoid Otri <= Units(O^triangle(A)); the repo has O^triangle and tau
   but no Otri positivity/log-shell condition;
2. an actual bad-place split Frobenioid instance for the native source T at
   each bad lift b (the repo has SplitFrobenioidPresentation but no instance
   tied to T/b);
3. the structural-sheaf/root-stack condition expressing that this Otri is the
   paper O^tri(T_x) and that the q_v^{1/2l} section lies in it.

## S357 exact spec

OtrianglerightOnSplitFrobenioid S:
* S : Iut.SplitFrobenioidPresentation;
* baseObject : S.frobenioid.carrier;
* Otri : Submonoid (Units (O^triangle(baseObject)));
* qSection, rootSection : Otri;
* rootSection ^ (2*l) = qSection;
* structuralSheafCondition : Prop (the missing paper condition).

OtrianglerightStructuralSheafRequired S := Nonempty spec.

No inhabitant is asserted.  OtriangleMonoid and OtimesUnits merely name the
existing O^triangle/O^times carriers.  No carrier is identified with
Completion or L.

No inequality, no fake root/carrier.
