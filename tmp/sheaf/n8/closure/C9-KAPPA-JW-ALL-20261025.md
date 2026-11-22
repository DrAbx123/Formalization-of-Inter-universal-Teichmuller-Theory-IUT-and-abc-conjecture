# C9 kappa via all JW relations: exact relation, no numeric kappa

Task: task-282. Owner: kummer. Date: 2026-10-25.
Short theorem/proof; no Lean/Project edits, no arbitrary data.
Only this file written. target_accepted=false; P6 open.

## 0. Inputs and scope

- Kondo 2025 local snapshot,
  sources/Kondo-2512.09231v1.html,
  SHA256 ff39006cf92ec22e1a39caa89fee9b86080953861d7ac6405e6919338c5c9e6f;
  Theorem D presentation at the "Theorem D" location, relations (3) and (4).
- C9-NEW-BI-SOURCE-20261025.md (task-250), 235 lines,
  SHA256 a90cc1b516a9afc784a20a8ce2fafb6cf16752459d73562d36c3093b85b294b3.
- C9-KAPPA-NEW-20261025.md (task-273), 162 lines,
  SHA256 fa921daf4b0a1027578b50a681d1e17c01736fc010231f940bb93d045ce322fc.
- C9-ZP-BASIS-THEOREM-20261025.md (task-255), 253 lines,
  SHA256 f7fca7b4336497d954a711d79033df56c046faa2caabe8ff436f9b8046c30e3a.

The JW presentation in Kondo 2025 Theorem D has only two relations:

    (3) sigma tau sigma^{-1}=tau^{p^f};
    (4) sigma x0 sigma^{-1}
          = (x0')^t x1^{p^s} [x1,x1'][x2,x3]...[x_{d-1},x_d],
        with x0' in closure<tau,x0>, x1' in closure<sigma,tau,x1>.   (0.1)

No other relations are imposed on x1,...,xd. This is the key to the all-relations
attack.

## 1. Theorem

Theorem 1.1 (JW-F all-relations theorem). Let F be the Kondo map to k_+, and
assume only the presentation (0.1). Then:

(a) F(tau)=0 (proved, not assumed);
(b) y0:=F(x0) is nonzero, F(x0')=n y0 for some n in Z_p, and

    (1-tn)y0 = p^s y1,  hence  y1 = lambda y0,
    lambda=(1-tn)/p^s in Q_p^times;                               (1.1)

(c) the kappa invariant is invariant along this relation:

    kappa(y1)=kappa(y0),                                          (1.2)

where kappa(y)=e v_p(Tr y)-v_pi(y) for y in J with Tr(y)!=0;
(d) no further linear relation on y1,...,yd or y0 follows from (3)-(4).

Consequently all JW relations together still do **not** compute kappa. They
reduce the unknown from (y1,y0) to the single extra-generator F-image y0 and
the scalar n; neither is supplied by the frozen source.

## 2. Proof

### 2.1 Relation (3): F(tau)=0

Apply F to sigma tau sigma^{-1}=tau^{p^f}. Since F is a homomorphism into the
additive group,

    F(sigma)+F(tau)-F(sigma)=p^f F(tau).                          (2.1)

The left side is F(tau), so (1-p^f)F(tau)=0. In Q_p,
1-p^f !=0 (p=12301, p^f ==0 mod p, so p^f !=1). Hence F(tau)=0. This proves
the “unit/root-of-unity log” assumption used in earlier attempts. QED.

### 2.2 Relation (4): y0 is a scalar multiple of y1

Apply F to (4). The commutators are killed; powers scale:

    F(sigma x0 sigma^{-1})=F(x0)=y0,
    F((x0')^t)=t F(x0'),
    F(x1^{p^s})=p^s y1.                                          (2.2)

Thus

    y0=t F(x0')+p^s y1.                                          (2.3)

Because x0' lies in closure<tau,x0> and F(tau)=0, F(x0') lies in the closed
Z_p-span of F(x0)=y0; write F(x0')=n y0 with n in Z_p. Then

    y0=t n y0+p^s y1,
    (1-tn)y0=p^s y1.                                             (2.4)

If y0=0, then p^s y1=0, contradicting y1!=0; so y0!=0. If 1-tn=0, again
y1=0; hence lambda=(1-tn)/p^s is nonzero and y1=lambda y0. QED.

### 2.3 Kappa invariance

For any nonzero lambda in Q_p and y in J with Tr(y)!=0:

    v_pi(lambda y)=v_pi(lambda)+v_pi(y),
    v_p(Tr(lambda y))=v_p(lambda)+v_p(Tr y),                     (2.5)

because pi^e=p u, e=41, and v_pi(lambda)=e v_p(lambda). Therefore

    kappa(lambda y)
      = e[v_p(lambda)+v_p(Tr y)] - [v_pi(lambda)+v_pi(y)]
      = e v_p(Tr y)-v_pi(y) = kappa(y).                          (2.6)

With lambda as in (1.1), kappa(y1)=kappa(y0). QED.

### 2.4 No further relations

The presentation has relations (3) and (4) only. Relation (3) gives F(tau)=0;
relation (4) gives (2.4). The conditions x0' in closure<tau,x0> and
x1' in closure<sigma,tau,x1> enter only through F(x0')=n y0 and
F(x1')=m y1; the commutator [x1,x1'] is killed by F, so m does not appear.
No relation among x1,...,xd remains. Hence no further linear equation on y0,
y1,...,yd is produced. QED.

## 3. What the theorem does and does not determine

The all-relations attack does determine:

- F(tau)=0;
- y1 lies on the same Q_p-line as y0=F(x0);
- kappa(y1)=kappa(y0);
- the only scalar parameter is lambda=(1-tn)/p^s.

It does not determine:

- y0=F(x0) itself;
- n in Z_p (equivalently F(x0'));
- Tr(y0), v_pi(y0), v_p(Tr y0);
- kappa(y0)=kappa(y1);
- whether kappa lies in [1,40], <=0, or >=41.

Thus it sharpens the obstruction but does not compute actual kappa.

## 4. Models

The relation is compatible with both structural models:

- Model A: y1=p. Choose y0=y1 (lambda=1), t=1, s arbitrary? Then
  (1-n)y0=p^s y1 gives 1-n=p^s, n=1-p^s in Z_p; compatible. kappa=0,
  B=O_K.
- Model B: y1=p+pi. Again choose y0=y1, n=1-p^s; kappa=40, B=I.

In both models F(x0')=n y0, and the relation is satisfied. The source does not
select lambda, y0, or kappa.

## 5. Exact missing input

The actual kappa is equivalent to any of:

- y0=F(x0) and n (equivalently F(x0'));
- lambda=(1-tn)/p^s and y0;
- actual y1 and Tr(y1);
- v_pi(y1) and v_p(Tr y1);
- the integral change-of-basis from the y-basis to (p,pi,...,pi^40).

None is supplied by Kondo/JW/F/local reciprocity/trace pairing/integrality.
This is an exact source obstruction, not a negative computation.

## 6. Classification

| item | status |
|---|---|
| F(tau)=0 from JW relation (3) | PROVED |
| y1=lambda y0, lambda=(1-tn)/p^s | PROVED |
| kappa(y1)=kappa(y0) | PROVED |
| all JW relations exhausted by (3)-(4) | PROVED from Kondo Thm D |
| actual y0/n/lambda/Tr(y0) source-computed | NO |
| kappa in [1,40] or <=0 | NOT DETERMINED |
| B=I / B=O_K | NOT PROVED |
| JW all-relations attack determines kappa | NO; exact obstruction |

## 7. Conclusion

Applying F to all JW relations is a genuine new constraint: it proves
F(tau)=0, gives y1=lambda F(x0), and shows kappa(y1)=kappa(F(x0)). But the
presentation has no further relation among x1,...,xd; the extra generator x0
and the scalar lambda are not computed by the frozen source. Therefore actual
kappa and the B branch remain source-undetermined. The conditional kappa-B
dichotomy remains the only theorem: if kappa is in [1,40] then B=I; if
kappa<=0 then B=O_K. No branch is proved; no P6 sign follows (task-264).

No arbitrary data; no Lean/kernel closure; target_accepted=false; P6 open.

## 8. Status

- Short natural-language theorem/proof only; no Lean/Project edits.
- New JW-F relation F(tau)=0, y1=lambda y0, kappa invariance; exact
  obstruction to numeric kappa recorded.
- target_accepted=false.
