# C9 CANONICAL A-CHAIN SOURCE LEDGER

Date: 2026-10-25. Status: P6 OPEN. No Lean proof.
Purpose: record the exact source files/lines/hashes for A1/A2/A3/T_can.

## 0. Primary source

IUT III text:
  tmp/sheaf/n8/closure/sources/IUT-III.txt
  11456 lines, 566015 bytes,
  SHA256 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D

IUT III PDF:
  tmp/sheaf/n8/closure/sources/IUT-III.pdf
  1307865 bytes.

## 1. Source ranges used by A1/A2/A3

Def3.8(i) q-pilot/Theta-pilot objects: lines 6506-6544.
Def3.8(ii) LGP-link full poly-isomorphism: lines 6545-6590.
Prop3.9 packet/procession normalization and degree=log-volume: lines 6724-6877.
Remark3.9.5 holomorphic hull and Ob1-Ob9: lines 7529-7868.
Remark3.10.2 lower horizontal arrows: around 9509-9561.
Remark3.11.1 IPL/SHE/APT/HIS: lines 9505-9635.
Theorem3.11: lines 9270-9635.
Cor3.12 statement / Theorem B: lines 10152-10180 (also 1155-1184).
Cor3.12 proof reduction: lines 10181-10242.
Steps (i)-(x): lines 10248-10569.
Step (xi-a) q-pilot representation: lines 10571-10581.
Step (xi-b)-(xi-c) output/IPL/SHE: lines 10582-10649.
Step (xi-d) determinant/log-volume: lines 10641-10681.
Step (xi-e)-(xi-f) fixed q value inclusion/inequality: lines 10682-10715.
Step (xi-g)-(xii): lines 10716-10801.

## 2. C9 canonical A-chain files

A1: C9-CAN-A1-20261025.md
  74 lines, SHA256 7EEF9990BA80160762113626831B5C51AB1B37E7CF09ADD3AC7B88D7D37EFCF6
  statement: full-poly class + Q_pilot + Q_can + 0-column.

IPL: C9-COR312-IPL-20261025.md
  242 lines, SHA256 0C5FD9F3CEFE18BFAC2EEFFE7F6494BCA40F21C37DD8118FAA6511AF3B8B13CD
  output-to-q-pilot full-poly link.

A2: C9-CAN-A2-20261025.md
  223 lines, SHA256 32B7E0BB8AA969808CD453F0AC97A7B05817268A16521D9DCF88B29B85B8CC7D
  normalized ratio identity; canonical absolute value is a source gap.

A3: C9-CAN-A3-20261025.md
  136 lines, SHA256 39F60CB82EED62910FB426341A4DB4FBCEEE84D43B62FC91CE9E54AE5313818D
  exact membership route; G1 'perhaps up to approximation' gap.

T_can: C9-CAN-TCAN-20261025.md
  203 lines, SHA256 5CCCCDBFCB8D9F2828884471966CE82C7A80C65BA2BE82B3E1B76C601598709C
  C9Hull=IIIHull and C9QPilot=IIIQPilot; not proved, definitional or comparator.

Independent A2/A3 audit: C9-CAN-A23-AUDIT-20261025.md
  107 lines, SHA256 266764A6F6CF77E7E035F489C8BE8052225D8C9DA9B17B4C76E6479673F8A761

## 3. Lean C6 normalization sources

ArithmeticTensorTupleBlock: finite p-adic tensor, no arch component.
  LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTensorBlocks.lean:26.
arithmeticTupleNormalizedLogVolume: finite-block 1/D normalization.
  LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedUnitScalingLogVolume.lean:89-98.
C6ActualIQData normalized weight 1/finrank:
  LeanFormal/IUT/ABCBridge/Geometry/C6ActualIQData.lean:30-43.

Consequence: h_C=h_bad_can/d+h_inf, not h_can/d globally.

## 4. Natural-language completion plan for A1/A2/A3

A1: source-exact at class/object level. Finish by declaring Q_pilot as
the canonical Frobenioid object and Q_can=-|log q|; no construction needed.

A2: do not require canonical absolute -|logTheta|. The ratio identity
  deg_nu(L_H)/M = deg_nu(det E_H)=mu_log_nu(H)=-|logTheta|_nu
  deg_nu(L_q)=-|log q|_nu
is enough: P6 inequality is invariant under common normalization c.
The remaining G1-G7 are source expansions of the ratio identity, not
target/normalization changes.

A3: exact membership Q_can in R_{<=h_can} is the source-supported route.
The only hard gap is IUT III's 'perhaps only up to approximation'. Either
(i) prove the exact membership/closure, or (ii) derive a signed error
epsilon with a proved bound. No arbitrary epsilon allowed.

T_can: for paper P6_can, define C9 target objects as the source objects;
then T_can is definitional. For the Lean normalized candidate, T_can needs
a comparator/normalization theorem; it cannot be assumed.

## 5. Status

A1: source-input smooth.
A2: ratio identity smooth at inequality level; absolute canonical identity open.
A3: exact membership open at approximation gap G1.
T_can: definitional for paper target, comparator for Lean normalized target.
P6_can: conditional on A2 ratio + A3 exact + T_can.
P6: OPEN. target_accepted=false.