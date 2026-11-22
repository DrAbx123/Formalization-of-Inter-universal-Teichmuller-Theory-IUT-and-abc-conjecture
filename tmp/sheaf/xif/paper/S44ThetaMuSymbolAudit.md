# S44: audit of Theta/theta, mu_2l/mu(F_mod^x), script-O/text-O

Date: 2026-10-29. Lean/source symbol audit only.

## 1. Theta (uppercase) versus theta (lowercase)

| Paper signifier | Meaning | Lean objects | Status |
|---|---|---|---|
| uppercase Theta | Theta-pilot / Theta-link object | ThetaPilotCarrier, ThetaLinkActual, ThetaPilotHull* | uppercase object family |
| lowercase theta | theta function / theta special values | thetaPacket (FiniteThetaPacket), thetaValueAt, realThetaValue, thetaPacket.scale | lowercase value/packet family |

Lean identifiers are case-sensitive and the carriers are different types:

* ThetaPilotCarrier l is Fin (lStar l.value + 1), a finite procession carrier;
* FiniteThetaPacket l is a packet record with q, scale and logVolume;
* ThetaLinkActual is a link object, not a theta value;
* thetaValueAt returns Real, not a Theta-pilot carrier.

No type alias or coercion identifies ThetaPilotCarrier/ThetaLinkActual with
FiniteThetaPacket/thetaValueAt.  The remaining risk is name-level: both families
live in overlapping namespaces and both names start with Theta/theta.

Exact name-level collision marker: ThetaPilotCarrier and thetaPacket are not the
same type, but a reader can confuse the Theta-pilot object with the theta packet.
No Lean equality between them exists or is asserted.

## 2. mu_2l versus mu(F_mod^x)

Actual local mu_2l carriers in the tree:

* muTwoLRoots (TwoLthRootQVActual): Set of units in Completion place satisfying
  zeta^(2l)=1;
* muTwoLAlgClosed (TwoLthRootKummerActual): Set of units in
  AlgebraicClosure(Completion place) satisfying zeta^(2l)=1;
* muTwoLRoots/muTwoLFactor in PaperThetaRootObstructionActual:
  rootsOfUnity (2*l) in sourceRootField;
* PaperSixTorsionCarrier: rootsOfUnity 6 in AlgebraicClosure F (a different
  torsion order, six-slot carrier).

Actual finite-field roots: the generic Mathlib rootsOfUnity n R applies to
F_mod as well, but the tree does not construct a dedicated mu(F_mod^x) group
object for the paper F_mod^x.  There is no theorem/alias identifying
rootsOfUnity n F_mod with any local Completion/AlgebraicClosure mu_2l carrier.

Exact type distinction: F_mod is a number field (Field/NumberField), while
Completion place and AlgebraicClosure(Completion place) are completions/closure
fields.  Their unit groups are different types, so rootsOfUnity has different
carriers.  The same identifier rootsOfUnity is generic over the carrier; it is
not a collapsed type.

Missing actual object: a dedicated paper mu(F_mod^x) root group and any map to
the local mu_2l.  No such map is constructed or asserted.  This is an exact gap,
not a collision.

## 3. script O versus text O

| Paper signifier | Meaning | Lean objects | Status |
|---|---|---|---|
| CMSY script O | ring of integers / integral structure | CompletionIntegers, integralClosure Z_p Block | script/integral carriers |
| text O | ordinary text O in prose | not a value automatically | no Lean type |

The script O objects are CompletionIntegers (valuation rings of completions) and
integralClosure Z_p (integral lattice of the tensor block).  They are not the
number-field RingOfIntegers (text O_k) unless a source map is supplied.  No
theorem identifies CompletionIntegers/integralClosure with the text-ring
RingOfIntegers.

Exact risk: both are called O and both are rings, but their carriers differ
(Completion place vs NumberField.RingOfIntegers K vs integralClosure in the
tensor block).  No type collapse is present; no wrapper is required for the
current consumers.

## 4. Conclusion

No Lean type/alias collision was found in these three symbol families.  The
actual risks are name-level and the missing dedicated mu(F_mod^x) object.
No fake wrapper, coercion, equality, axiom, or sorry is introduced.
