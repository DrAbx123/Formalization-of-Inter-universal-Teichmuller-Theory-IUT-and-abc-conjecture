# C9 adversarial review: A3 CL1-CL3

Task: task-409. Date: 2026-10-25. Reviewer: transport.
Review only; no rewriting of A3. No Lean; no mixed/E3; no arbitrary.
Only this file written. target_accepted=false.

## 0. Inputs reviewed

| file | lines | SHA256 |
|---|---:|---|
| C9-CAN-A3-SUBQUOTIENT-EXPANDED-20261025.md | 142 | BB1C9A50C6E2037F8C62DCD43630AC3DE18D8DB15D2FA53079AD715604737F0B |
| C9-P6-CAN-NATURAL-PROOF-20261025.md | 162 | E78BAD81B1ABE4CD365D77391888C7B4DC74A3B3CC4E5FC83E8F21EB7B58A1C9 |
| C9-CAN-A3-20261025.md | 136 | 39F60CB82EED62910FB426341A4DB4FBCEEE84D43B62FC91CE9E54AE5313818D |

Source: IUT-III.txt SHA256 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.

## 1. Overall verdict

A3 as written is a source-faithful restatement of the closed-loop/AND argument
of IUT III Remark 3.9.5(vii)(ix) and Remark 3.12.2(citw)/(fitw). It is NOT an
independent derivation of Q_can in R_{<= h_can} from CL1-CL3.

No logical contradiction or counterexample was found. The defects are:
- one non-sequitur in CL2.3 (individual compatibility does not compose to the
  closed loop);
- one false compatibility claim in CL3.3 (sQ5 is explicitly incompatible with
  F^units-times-mu data, not compatible with CL1/CL2);
- one overstatement in CL1.4 (q-pilot is not an output of the formal quotient);
- one circular/restatement step in CL3.5 (membership is exactly Cor3.12
  xi-e/f, not derived by CL3.1-CL3.4).

If A3 is labeled "source-conditional, assuming Ob9-1, cQ3/cQ4, Remark3.9.5(ix),
Cor3.12(xi-e)-(xi-f)", it is acceptable. If A3 is labeled "expanded proof that
closes A3", it is REJECTED at CL2.3, CL3.3, CL3.5.

## 2. CL1 per-step verdicts

### CL1.1 — ACCEPT

Source: Ob5 (lines 7922-7943): the passage to comparable objects via
det^otimes M of a suitable hull produces objects in the local/global
Frobenioids of the codomain F^value-times-mu-prime-strip. This is exactly what
CL1.1 states. No gap at the restatement level.

### CL1.2 — ACCEPT

Source: Ob9-1 (lines 8145-8161): the tensor-power-twist indeterminacies
(Ob4-3), the upper-semi-compatibility formalism (Ob5), and arbitrary log-link
iterates (Ob8) "have no effect on the comparability of the objects obtained in
(Ob5)"; they function as compatibility conditions for coarse invariants such
as log-volume. CL1.2 accurately quotes this.

### CL1.3 — ACCEPT

Source: Ob9 (lines 8128-8144): passing to realified semi-simplifications is a
quotient operation on both domain and codomain of the log-link that induces a
natural bijection between log-volumes of hulls in domain and codomain. CL1.3
accurately quotes this.

### CL1.4 — QUALIFY / PARTIAL REJECT

Claim: "Therefore the formal indeterminacy quotient acts compatibly with the
log-volume readout; the log-volume of the Theta-hull and the q-pilot value are
well-defined on this quotient."

Problem: Ob9-1 concerns the objects obtained in Ob5, i.e. the determinant/hull
objects. It does not say that the q-pilot value is an object of that quotient.
The q-pilot is the external fixed input line bundle (A1); its log-volume is
defined before and independently of the quotient. The sentence conflates:

- comparability of the Theta-hull determinant objects on the quotient, and
- well-definedness of the q-pilot value.

The compatibility statement is acceptable for the Theta-hull side; the q-pilot
side is fixed by A1, not by CL1.4. This is a wording overreach, not a
mathematical contradiction.

## 3. CL2 per-step verdicts

### CL2.1 — ACCEPT

Source: (cQ3), lines 8264-8345: hulls are stabilized by O_K^times; a positive
tensor power of the determinant gives objects det^otimes M(phi(P_B)) in the
local/global Frobenioids of the codomain; pull-back morphisms give natural
faithful actions by G_v and O^times_mu; this is the F^units-times-mu-prime-strip
portion. CL2.1 is a faithful summary.

### CL2.2 — ACCEPT

Source: (cQ4), lines 8346-8358: the vertical-shift adjustment is obtained by
the log-Kummer correspondence and is tautologically compatible with suitable
isomorphisms between G_v and O^times_mu(G_v) / O^times_mu_Fv, up to arbitrary
log-link iterates. CL2.2 is a faithful summary.

### CL2.3 — REJECT AS INFERENCE

Claim: "Therefore the chain of poly-isomorphisms that passes through sQ3/sQ4
is compatible with the log-Kummer correspondence; this is (cQ3),(cQ4)."

This does not follow from CL2.1 + CL2.2. The source properties (cQ3), (cQ4)
say that the individual operations sQ3, sQ4 are compatible with the
F^units-times-mu-prime-strip data. They do not assert that the **composite
chain** through sQ1, sQ2, sQ3, sQ4 is a closed loop of poly-isomorphisms.
That closed-loop statement is a separate source assertion in Remark3.9.5(ix),
lines 8383-8431, not a consequence of (cQ3)/(cQ4).

The word "therefore" is a non-sequitur. The correct statement is:

- (cQ3), (cQ4) => each of sQ3, sQ4 is compatible with the relevant
  F^units-times-mu data;
- the closed loop requires the additional source assertion of Remark3.9.5(ix).

CL2.3 may be accepted only if it is explicitly labeled as quoting
Remark3.9.5(ix), not as following from CL2.1/CL2.2.

## 4. CL3 per-step verdicts

### CL3.1 — ACCEPT (source-conditional)

Source: Remark3.9.5(ix), lines 8383-8405: the chain that begins with the
q-pilot in the codomain, passes through the LGP-link to the domain, through
sQ1/sQ2 poly-isomorphisms, and finally through sQ3/sQ4, forms a closed loop up
to the formal quotient indeterminacies. CL3.1 accurately restates this.

Caveat: this is a source assertion of a closed loop, not a construction
algorithm written out in the expanded file. Accept only as source quote.

### CL3.2 — ACCEPT (source-conditional)

Source: Remark3.9.5(ix), lines 8417-8424: the closed loop constructs an
F^value-times-mu-prime-strip that is "simultaneously equipped with two
intertwinings", namely the Theta-intertwining up to indeterminacies and the
q-intertwining. This is exactly the AND statement. CL3.2 is acceptable as a
restatement.

### CL3.3 — REJECT

Claim: "sQ5 (log-volume/realified semi-simplification) passes to the coarse
log-volume invariant, compatible with CL1/CL2."

Problem: source (iQ5), lines 8359-8366, states the opposite qualitative
property:

    (iQ5) Incompatibility of (sQ5) with F^units-times-mu-prime-strip data:
    passing to log-volumes amounts precisely to forgetting the local Galois
    groups and Frobenius-like units.

sQ5 is deliberately **not** compatible with the F^units-times-mu data. It is
applied only after the closed loop through sQ3/sQ4, precisely because it
forgets that data. Therefore CL3.3 cannot say sQ5 is compatible with CL1/CL2;
it should say sQ5 is the final coarse quotient that is applied after the
compatible sQ3/sQ4 stage, and its incompatibility with F^units-times-mu is
what makes it a log-volume readout.

This is a substantive overstatement, not a wording issue.

### CL3.4 — ACCEPT (source-conditional)

Source: Remark3.9.5(ix), lines 8406-8424, and Remark3.12.2(fitw), lines
10977-11022: the q-intertwining, and hence the q-pilot log-volume, is a
special case/projection of the Theta-intertwining up to indeterminacies.
CL3.4 is acceptable as a source restatement.

### CL3.5 — REJECT AS INDEPENDENT DERIVATION / ACCEPT ONLY AS RESTATEMENT

Claim: "Hence Q_can in R_{<= h_can}."

This is exactly the conclusion of Corollary 3.12(xi-e)-(xi-f), lines
10682-10715: -|log(q)| is in R_{<= -|log(Theta)|} because the construction of
possible output log-volumes includes the fixed q-pilot value. It is not
derived by CL3.1-CL3.4 alone:
- CL3.1-3.4 give a closed-loop prime-strip simultaneously equipped with the
  two intertwinings;
- the step from simultaneous intertwinings to the **specific membership**
  Q_can in R_{<= h_can} uses the Cor3.12 xi-e interpretation of expressibility
  under the fixed pilot-volume condition and xi-f's formal inclusion.

Thus CL3.5 is a restatement of the target step, not a new proof. If A3 is
presented as "expanded source extraction", this is acceptable with the
Cor3.12(xi-e)-(xi-f) citation. If presented as a derivation from CL1-CL3, it is
circular.

## 5. Summary table

| step | verdict | exact reason |
|---|---|---|
| CL1.1 | ACCEPT | Ob5 determinant/hull objects in codomain Frobenioids |
| CL1.2 | ACCEPT | Ob9-1 formal indeterminacies no effect on comparability |
| CL1.3 | ACCEPT | Ob9 realified semi-simplification bijection |
| CL1.4 | QUALIFY | q-pilot is fixed input, not an object of the formal quotient |
| CL2.1 | ACCEPT | cQ3 source restatement |
| CL2.2 | ACCEPT | cQ4 source restatement |
| CL2.3 | REJECT as inference | individual compatibility does not compose to closed loop; ix is separate |
| CL3.1 | ACCEPT conditional | ix closed loop source assertion |
| CL3.2 | ACCEPT conditional | ix simultaneous intertwinings |
| CL3.3 | REJECT | iQ5 says sQ5 is incompatible with F^units-times-mu data |
| CL3.4 | ACCEPT conditional | ix projection of Theta onto q |
| CL3.5 | REJECT unconditional | membership is Cor3.12(xi-e)-(xi-f), not derived from CL3.1-4 |

## 6. Exact logical gaps

(GAP1) CL2.3: the closed loop is not a consequence of (cQ3)/(cQ4); it is the
separate source assertion Remark3.9.5(ix), lines 8383-8431. The expanded file
uses the closed loop in CL3.1 without citing it as the independent input.

(GAP2) CL3.3: (iQ5) explicitly says sQ5 is incompatible with the
F^units-times-mu data. The review rejects the claim that sQ5 is compatible with
CL1/CL2; it is a coarse quotient applied after the closed loop.

(GAP3) CL3.5: membership Q_can in R_{<= h_can} is Cor3.12(xi-e)-(xi-f), not a
formal consequence of CL1-CL3. The proof needs the fixed pilot-volume
interpretation of SHE and the xi-f inclusion.

(GAP4) No counterexample: there is no known source-valid configuration in
which CL1-CL3 hold but Q_can > h_can. The objection is proof structure/
circularity, not falsity.

## 7. Final recommendation

A3 is acceptable as a **source-conditional restatement** if it is explicitly
labeled:

    assuming Ob9-1, cQ3/cQ4, Remark3.9.5(ix) closed loop, and
    Cor3.12(xi-e)-(xi-f), A3 holds.

A3 is **not acceptable as an independent expanded proof** because CL2.3,
CL3.3, and CL3.5 are not derived from the preceding steps. The source has the
closed-loop/AND assertion, but the expanded file does not formalize it; it
quotes it and then treats the target membership as a consequence.

No mixed/E3 profile, arbitrary data, or Lean edit was used.
target_accepted=false.
