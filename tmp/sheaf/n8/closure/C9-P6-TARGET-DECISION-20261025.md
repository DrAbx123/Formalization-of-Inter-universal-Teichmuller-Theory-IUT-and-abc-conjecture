# C9 P6 TARGET DECISION

Date: 2026-10-25. Status: P6 OPEN. Natural language only; no Lean.

## 0. Decision

PRIMARY and ONLY paper target: P6_can.

    P6_can: for every admissible C, Q_can <= h_can,

where Q_can = -|log q| and h_can = -|log Theta| are the canonical
packet+procession-normalized Cor3.12 log-volumes. These are the paper
objects; no auxiliary normalized object is introduced.

P6_norm is NOT the paper target. It is a C9/Lean-normalized surrogate:

    P6_norm: for every admissible C, Q_norm <= h_C,

with Q_norm=Q_can/d (d=41) and h_C = h_bad_can/d + h_inf.

It exists only because C6/Lean uses a degree-normalized finite-block
volume. It is not justified as a replacement for the paper object.

Exact relation:

    h_can = d*h_C - (d-1)*h_inf,
    Q_can = d*Q_norm,
    Cor3.12: Q_can <= h_can
    => Q_norm <= h_C - ((d-1)/d)*h_inf.

Thus P6_norm follows if h_inf>=0; if h_inf<0 it is not implied.
The mixed target Q_can<=h_C is invalid (off by d and arch).

## 1. Why P6_can is primary

- It is exactly IUT III Cor3.12 / Theorem B.
- It uses the paper objects Q_can/h_can; no invented object.
- No factor d and no arch sign ambiguity on the h side.
- The natural-language chain A1-A3 is structurally clean:
  fixed q-pilot input -> possible output linked by full polyiso ->
  hull/determinant/log-volume -> fixed q-pilot value in possible set ->
  Q_can <= h_can.
- P6_norm would require a separate arch lower bound h_inf>=0 and is a
  different statement. We should not replace paper P6 by P6_norm.

If the existing Lean candidate PaperP6C6AlignedTarget is stated in
normalized quantities, its semantic identification with paper P6_can must
be proved by a comparator/normalization theorem; it cannot be assumed.

## 2. Natural-language status of P6_can

A1: smooth source-input statement.
  A1 = (full-poly class of F^value x mu prime-strips, Q_pilot, -|log q|).
  q_v up to torsion is harmless; Q_pilot object and log-volume are
  independent of generators/torsion.

A2: exact identity statement:
  L_H = det^tensor M(E_H) tensor det^tensor M(O(-))^{-1},
  deg(L_H)/M = deg(det E_H) = mu_log(H) = -|log Theta|,
  deg(L_q) = -|log q|.
  Residual source gaps G1-G7: explicit E_H/det construction, O(-) degree
  details, M formula, weights N_v, hull approximant, vertical shift, tensor
  twist/upper-semi compatibility.

A3: exact membership route:
  -|log q| in R_{<=-|log Theta|}.
  Via L1 full-poly invariance of normalized pilot log-volume,
  L2 SHE-to-membership, L3 hull/log-volume monotonicity.
  Residual gap G1: IUT III says 'perhaps only up to some sort of
  approximation'; exact membership needs this semantic step.

Cor3.12: Q_can <= h_can.

## 3. Judgment

Logical skeleton of P6_can: SOUND. No circularity, no factor ambiguity,
no hidden target change. The remaining gaps are source-internal expansions
(A2 G1-G7, A3 L1-L3/G1), not conceptual holes.

However, natural language is not yet a complete proof: the A3 exact-vs-
approximation step and the A2 determinant details are still named gaps.
Therefore: do not claim P6_can proved; do not start Lean proof.

If A2 G1-G7 and A3 L1-L3/G1 are expanded, P6_can is the natural-language
theorem to formalize. P6_norm requires an additional h_inf>=0 theorem.

## 4. Formalization plan after expansion

Lean statements (only after expansion):
  P6Can: forall C, Qcan C <= hcan C
  P6NormOfArch: (forall C, 0 <= hInf C) -> forall C, Qnorm C <= hC C
  exact target: Qcan/d + ((d-1)/d)hInf <= hC
  mixed target obstruction: Qcan <= d*hC - (d-1)*hInf

No Lean statement should silently use P6_norm without the h_inf>=0
hypothesis or the arch-corrected target.

P6: OPEN. target_accepted=false.