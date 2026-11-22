# C9 adversarial review of the log-shell construction route to C1

Task ID: task-450 / C9-C1-LS-ADVERSARIAL-20261025. Reviewer: primespine. Date: 2026-10-25.
Object: tmp/sheaf/n8/closure/C9-C1-LOGSHELL-CONSTRUCTION-20261025.md (110 lines).
Scope: independent adversarial review; no rewriting; no Lean/Project edits; no mixed/E3; only this file written.

## 0. Verdict

**REJECT the log-shell construction as a proof of C1.** The route contains a container/type error in its own definitions, an unproved and source-incompatible N-action model, and a circular key claim (D). The alleged `S_q^LS` is not defined from the source at the required level; admissibility is asserted from the very compatibility being proved; and the final eta-to-output bridge is exactly C1. C1 remains open.

The only acceptable components are elementary conditional statements: Lemma A for nonzero pilots, and the abstract measure-quotient construction if its measure hypotheses are granted.

## 1. Step A (Rss/varying): CONDITIONAL, not proved

Step A defines Rss as adelic measurable subsets of the large container VC(I) modulo equal volume and claims vol:Rss->R_{>0} is a bijection. This requires:

- finite positive total measure and non-atomicity of Haar measure;
- existence of measurable subsets of every positive volume;
- quotient by volume being a bijection onto R_{>0}, including the correct normalization [T]=0/volume1 conventions.

None is proved. The claim 'Haar measure is non-atomic on the local factors' is plausible but not a proof for the adelic product/quotient. Also, if the class [T] is a pointed real line, the zero point and the 'nonzero iff volume nonzero' statement need the precise normalization; they are not established.

## 2. Step B (Rval, eta_q): CONDITIONAL

Step B defines eta_q by p_q -> [S_q] and extends linearly. This is a valid definition **if**:

- p_q is a nonzero pilot of Rval;
- S_q has finite positive volume in VC(I) and its class is nonzero;
- `{q_v O_v}` is indeed an adelic measurable subset/class of VC(I), not merely a formal diagonal.

These are not proved. The step assumes the q-pilot diagonal can be embedded in the large container with finite positive volume; LANA's q-pilot target class is a class in R^ss, but the identification with a concrete measurable subset of the large container is a compatibility step, not a definition.

## 3. Step C (S_q^LS): REJECT — not source-defined as claimed

Step C defines `S_q^LS subset VC(LS)` as the 'log-Kummer image' of the q-pilot value-group data in VC(LS), and asserts it is source-defined, adelic measurable, finite positive volume.

Exact problems:

1. **No source definition of this image as a subset of VC(LS).** IUT III Step (xi-d) describes a representation of the q-pilot object on `1,circ U_Q` via the 1-column log-Kummer correspondence; it does not define a subset `S_q^LS` of the small log-shell container VC(LS) with the stated properties. The log-Kummer correspondence is a comparison, not an image map with a measurable set as output.
2. **Container mismatch.** The q-pilot representation in xi-d is a region in the **large** 1-column container, not a canonical subset of VC(LS). Calling its 'log-Kummer image' a small-container subset is precisely the bridge that is missing.
3. **Measurability/adelicity/finite volume are asserted, not proved.** The log-Kummer correspondence is only upper semi-compatible (Ind3); it does not produce an adelic measurable set of finite positive volume.

Thus G1 is not an 'existence and properties' gap that can be filled later; the object itself is not defined by the cited source.

## 4. Step D (N/LGP action): REJECT — type error and unproved model

Step D defines

    T_1 : VC(I) -> VC(I),  U |-> LGP·U,                              (4.1)

and then uses `T_1(S_q^LS)` with `S_q^LS subset VC(LS)` (Step E). This is a **container/type error**: T_1 as defined has domain VC(I), not VC(LS). The route needs a map VC(LS)->VC(I); no such map is defined.

Further, Step D claims T_1 is a measurable bijection with constant Haar scaling. This is the same unproved hypothesis as the volume-scaling route:

- LANA/Theorem3.11 describe a construction algorithm, not a set-theoretic transport; APT explicitly warns against treating it as a map;
- the log-Kummer comparison is only upper semi-compatible (Ind3), not a bijection;
- the LGP action is local with weights/compact structures; a single constant Haar scaling is not source-supported.

### Key claim (D): REJECT/circular

Claim (D): `T_1(S_q^LS)` has the same class in Rss as `S_q`. This is exactly the q-pilot compatibility/xi-e statement the route is supposed to prove. The text calls it 'the compatibility of the log-Kummer representation with the LGP action, i.e. the q-pilot side of SHE/xi-e.' That is a restatement of the desired bridge, not a proof. No source theorem gives this class equality.

## 5. Step E (eta^anab, admissibility): REJECT — circular

Step E says `S_q^LS` is admissible because it is the source log-Kummer representation of the q-pilot and the anabelian N-action is defined on it.

Circularity:

- LANA's eta^anab_S requires S to be an admissible integral structure in VC(LS) (measurable, N-compatible, in the domain of the anabelian construction). Being a 'log-Kummer representation' does not establish any of these.
- 'The anabelian N-action is defined on it by Theorem3.11' is exactly what needs proof; Theorem3.11 defines the action on suitable mono-theta environments, not on an arbitrary q-defined region.
- The target pilot `[M]=[1·S_q^LS]` is used without proving M is defined or in Rss; with the type error of (4.1), M is not well-defined.

## 6. Step F (eta equality -> C1): REJECT — this is C1

Step F invokes xi-e/f to conclude there is an output D0 in O with logVol(D0)=Q. This is exactly the C1 bridge; the source's xi-e/f is the compatibility under question, not a proved existence theorem. The eta equality is an equality of pointed real-line isomorphisms; it does not by itself produce a possible output data element D0 of the multiradial algorithm, nor identify its log-volume with Q in the paper normalization.

The route therefore ends by assuming C1. It does not reduce it.

## 7. Additional hidden assumptions

- `S_q` finite positive volume and nonzero class in the large container.
- `S_q^LS` adelic measurable finite positive volume in the small container.
- A map VC(LS)->VC(I) extending T_1 and compatible with the LGP action.
- Constant Haar scaling of T_1.
- `1·S_q^LS` well-defined and in Rss.
- Nonzero pilots for Lemma A.

None is proved.

## 8. Accept/reject table

| item | verdict | exact reason |
|---|---|---|
| Step A measure quotient | CONDITIONAL | non-atomic/finite/all-volume bijection unproved |
| Step B eta_q | CONDITIONAL | S_q finite positive/adherent class unproved |
| Step C S_q^LS | REJECT | not source-defined as VC(LS) subset; measurability/adelicity/volume asserted |
| Step D T_1/container | REJECT | domain type error VC(I) vs VC(LS); bijection/constant scaling unproved; APT conflict |
| Claim (D) | REJECT | exactly the desired q-pilot compatibility; circular |
| Step E admissibility | REJECT | circular: log-Kummer representation != admissible integral structure |
| Step F output bridge | REJECT | C1 itself; eta equality does not give D0 |
| Lemma A | ACCEPT conditionally | correct only with nonzero pilots; nonzero not established |

## 9. Final review verdict

**REJECT the log-shell construction route as a proof of C1.** The route has a container/type error, no source-defined `S_q^LS`, an unproved N-action model in conflict with APT/Ind3, a circular key equality (D), circular admissibility, and an output bridge that is exactly C1. C1 remains open. No mixed/E3; no Lean.

target_accepted=false.
