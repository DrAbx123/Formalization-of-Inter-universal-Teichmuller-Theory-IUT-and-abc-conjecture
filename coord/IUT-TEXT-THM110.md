# IUT-TEXT-THM110 — verbatim IUT IV, Theorem 1.10 excerpts (A1037)

Source PDF: `papers/motizuki_corpus/raw/Inter-universal Teichmuller Theory IV.pdf`.
Extraction: `tools/pdftotext_iut.py` -> `coord/IUT-TEXT/IV.txt` (pypdf, page markers).
Quotes below are verbatim from the extracted text; page numbers are PDF page markers.

## 1. The normalization |log(q)| = (1/(2l))·log(q) (p. 23)

> Here, we observe that the various “log(q(−))’s” are
> independent of the choice of F□, and that the quantity “|log(q)|∈ R_{>0}” defined in
> [IUTchIII], Corollary 3.12, is equal to  1/(2l) · log(q) ∈ R  [cf. the definition of
> “q_v” in [IUTchI], Example 3.2, (iv)].

(PDF p. 23; this is the explicit `1/(2l)` normalization used in our C-line.
`log(q)` here is the arithmetic degree `deg(q_F□^ADiv)` defined on p. 23.)

## 2. Theorem 1.10 statement (pp. 22-23)

> Theorem 1.10. (Log-volume Estimates for Θ-Pilot Objects) Fix a col-
> lection of initial Θ-data as in [IUTchI], Definition 3.1. Suppose that we are
> in the situation of [IUTchIII], Corollary 3.12, and that the elliptic curve E_F has
> good reduction at every valuation ∈ V(F)_good ⋂ V(F)_non that does not divide
> 2l. In the notation of [IUTchI], Definition 3.1, let us write d_mod := [F_mod : Q],
> (1 ≤) e_mod (≤ d_mod) for the maximal ramification index of F_mod [i.e., of valu-
> ations ∈ V^non_mod] over Q, d*_mod := 2^12 · 3^3 · 5 · d_mod, e*_mod := 2^12 · 3^3 · 5 · e_mod
> (≤ d*_mod), and F_mod ⊆ F_tpd := F_mod(E_Fmod[2]) ⊆ F ...
> Moreover, we assume that the (3·5)-torsion points of E_F are defined over F, and
> that F = F_mod(√−1, E_Fmod[2·3·5]) := F_tpd(√−1, E_Ftpd[3·5]) ...
> [Thus, ... from [IUTchI], Definition 3.1, (c), that l ≠ 5.] If F_mod ⊆ F□ ⊆ K is any
> intermediate extension which is Galois over F_mod, then we shall write ...
> log(q_v) := deg_{V(F□)_v}(q_F□^ADiv) ∈ R_{≥0}; log(q_vQ) := deg_{V(F□)_vQ}(q_F□^ADiv) ∈ R_{≥0}
> log(q) := deg(q_F□^ADiv) ∈ R_{≥0} ...
> Then one may take the constant “C_Θ ∈ R” of [IUTchIII], Corollary 3.12, to be
> (l+1)/4 · |log(q)| · { (1 + 12·d_mod/l)·(log(d_Ftpd) + log(f_Ftpd)) + 10·(e*_mod·l + η_prm)
> − 1/6·(1 − 12/l²)·log(q) } − 1
> and hence, by applying the inequality “C_Θ ≥ −1” of [IUTchIII], Corollary 3.12,
> conclude that
> 1/6·log(q) ≤ (1 + 20·d_mod/l)·(log(d_Ftpd) + log(f_Ftpd)) + 20·(e*_mod·l + η_prm)
> ≤ (1 + 20·d_mod/l)·(log(d_F) + log(f_F)) + 20·(e*_mod·l + η_prm)
> — where η_prm is the positive real number of Proposition 1.6.

(PDF pp. 22-23.)

## 3. Proof Step (iv): upper bound for the procession-normalized hull log-volume (p. 27)

> (iv) In order to estimate the constant “C_Θ” of [IUTchIII], Corollary 3.12, we
> must, according to the various definitions given in the statement of [IUTchIII],
> Corollary 3.12, compute an upper bound for the
> procession-normalized mono-analytic log-volume of the holomorphic hull
> of the union of the possible images of a Θ-pilot object, relative to the
> relevant Kummer isomorphisms [cf. [IUTchIII], Theorem 3.11, (ii)], in
> the multiradial representation of [IUTchIII], Theorem 3.11, (i), which we
> regard as subject to the indeterminacies (Ind1), (Ind2), (Ind3) described
> in [IUTchIII], Theorem 3.11, (i), (ii).
> Thus, we proceed to estimate this log-volume at each vQ ∈ VQ. Once one fixes vQ,
> this amounts to estimating the component of this log-volume in
> “IQ(S±_{j+1}; n,◦D⊣_{vQ})” [cf. the notation of [IUTchIII], Theorem 3.11, (i), (a)],
> for each j ∈ {1,...,l⋇}, which we shall also regard as an element of F⋇_l, and then
> computing the average, over j ∈ {1,...,l⋇}, of these estimates. Here, we recall
> [cf. [IUTchI], Proposition 6.9, (i); [IUTchIII], Proposition 3.4, (ii)] that
> S±_{j+1} = {0,1,...,j}. Also, we recall from [IUTchIII], Proposition 3.2, that
> “IQ(S±_{j+1}; n,◦D⊣_{vQ})” is, by definition, a tensor product of j+1 copies, indexed
> by the elements of S±_{j+1}, of the direct sum of the Q-spans of the log-shells
> associated to each of the elements of V(F_mod)_{vQ} ... In particular, for each
> collection {v_i}_{i∈S±_{j+1}} of [not necessarily distinct!] elements of V(F_mod)_{vQ},
> we must estimate the component of the log-volume in question corresponding to the
> tensor product of the Q-spans of the log-shells associated to this collection
> {v_i}_{i∈S±_{j+1}} and then compute the weighted average [cf. the discussion of
> Remark 1.7.1], over possible collections {v_i}_{i∈S±_{j+1}}, of these estimates.

(PDF p. 27.)

## 4. Proof Step (v): the estimate and the j-average (pp. 27-29)

> (v) Let vQ ∈ V_dst_Q. Fix j, {v_i}_{i∈S±_{j+1}} as in Step (iv). Write v_i ∈ V ∼→ V_mod =
> V(F_mod) for the element corresponding to v_i. We would like to apply Proposition
> 1.4, (iii), to the present situation, by taking
> · “I” to be S±_{j+1};
> · “I* ⊆ I” to be the set of i ∈ I such that e_{v_i} > p_{vQ} − 2;
> · “k_i” to be K_{v_i} [so “R_i” will be the ring of integers O_{K_{v_i}} of K_{v_i}];
> · “i†” to be j ∈ S±_{j+1};
> · “λ” to be 0 if v_j ∈ V_good;
> · “λ” to be “ord(−)” of the element q^{j²}_{v_j} [cf. the definition of “q_v” in
>   [IUTchI], Example 3.2, (iv)] if v_j ∈ V_bad.
> Thus, the inclusion “φ(p^λ · (R_I)∼) ⊆ p^{⌊λ−d_I−a_I⌋}· log_p(R×_I)” of Proposition
> 1.4, (iii), implies that the result of multiplying “p^{⌊λ⌋−|I|} · 2^{−|I|} · log_p(R×_I)”
> by a suitable nonpositive [cf. the inequalities concerning “d_I+a_I” that constitute
> the final portion of Proposition 1.4, (iii)] integer power of p_{vQ} contains the
> “union of possible images of a Θ-pilot object” discussed in Step (iv). That is to say,
> the indeterminacies (Ind1) and (Ind2) are taken into account by the arbitrary nature
> of the automorphism “φ” [cf. Proposition 1.2], while the indeterminacy (Ind3) is
> taken into account by the fact that we are considering upper bounds [cf. the
> discussion of Step (x) of the proof of [IUTchIII], Corollary 3.12], together with
> the fact that the above-mentioned integer power of p_{vQ} is nonpositive, which
> implies that the module obtained by multiplying by this power of p_{vQ} contains
> “p^{⌊λ⌋−|I|} · 2^{−|I|} · log_p(R×_I)”. Thus, an upper bound on the component of the
> log-volume of the holomorphic hull under consideration may be obtained by computing
> an upper bound for the log-volume of the right-hand side of the inclusion
> “p^{⌊λ−d_I−a_I⌋·log_p(R×_I)} ⊆ p^{⌊λ−d_I−a_I⌋−b_I}·(R_I)∼” of Proposition 1.4, (iii).
> Such an upper bound
> ( −λ + d_I + 1 )·log(p) + ∑_{i∈I*} {3 + log(e_i)}
> is given in the second displayed inequality of Proposition 1.4, (iii). Here, we
> note that if e_{v_i} ≤ p_{vQ} − 2 for all i ∈ I, then this upper bound assumes the
> form “( −λ + d_I + 1 )·log(p)”. ...
> Here, we note that it follows immediately from the first equality of the first
> display of Proposition 1.7 that, after passing to weighted averages, the operation
> of symmetrizing with respect to the choice of “i† ∈ I” in S±_{j+1} does not affect
> the computation of the upper bound under consideration. Thus, by applying
> Proposition 1.7, we obtain that the resulting “weighted average upper bound” is
> given by
> (j+1)·log(d^K_{vQ}) − j²/(2l)·log(q_{vQ}) + log(s^Q_{vQ}) + 4(j+1)·l*_mod·log(s^≤_{vQ})
> — where we recall the notational conventions introduced in Step (iii). Thus, it
> remains to compute the average over j ∈ F⋇_l. By averaging over
> j ∈ {1,...,l⋇ = (l−1)/2} and applying (E1), (E2), we obtain the
> “procession-normalized upper bound”
> (l⋇+3)/2·log(d^K_{vQ}) − (2l⋇+1)(l⋇+1)/(12l)·log(q_{vQ}) + log(s^Q_{vQ})
> + 2(l⋇+3)·l*_mod·log(s^≤_{vQ})
> = (l+5)/4·log(d^K_{vQ}) − (l+1)/24·log(q_{vQ}) + log(s^Q_{vQ})
> + (l+5)·l*_mod·log(s^≤_{vQ})
> ≤ (l+1)/4 · { (1 + 4/l)·log(d^K_{vQ}) − 1/6·log(q_{vQ}) + 4/l·log(s^Q_{vQ})
> + 20/3·l*_mod·log(s^≤_{vQ}) }
> — where, in the passage to the final displayed inequality, we apply the estimates
> 1/(l+1) ≤ 1/l and 4(l+5)/(l+1) ≤ 20/3, both of which may be regarded as
> consequences of the fact that l ≥ 5.

(PDF pp. 27-29.)

## 5. Mapping to our C-line notation

- IUT `log(q)` = arithmetic degree `deg(q_F□^ADiv)` (weighted q-parameters);
  IUT `|log(q)| = (1/(2l))·log(q)` (p. 23).
- Our `A = absLogQ = logQ/(2ℓ)` is exactly this normalization (lana
  `LeftHandSide.lean:81-88` derives `logQ = ∑ weight·qOrder·log p` and divides
  by `2ℓ`).
- IUT `−|log(Θ)|` is the procession-normalized log-volume of the holomorphic
  hull of the union of possible Θ-pilot images, subject to Ind1/Ind2/Ind3; this
  is our `R` (up to sign: our `R = -rhs` with `rhs = -|log Θ|`).
- Step (iv) says: compute an **upper bound** on the log-volume of the hull;
  Step (v) computes it componentwise at `vQ`, with the key q-term
  `− j²/(2l)·log(q_{vQ})` before averaging, and `−(l+1)/24·log(q_{vQ})` after the
  `j`-average.  This is the paper source of the `j²/(2ℓ)` and `(sF−1)`-type
  coefficients used in our decomposition.
- The final Theorem 1.10 bound is `1/6·log(q) ≤ ...`, obtained from
  `C_Θ ≥ −1`; it is an inequality, not an equality for `R`.

## 6. Status

- Extract script: `tools/pdftotext_iut.py`; outputs `coord/IUT-TEXT/I.txt`,
  `II.txt`, `III.txt`, `IV.txt` with page markers.
- Quotes above are from the PDF text layer; OCR/page-break artifacts (line
  breaks, missing spaces) are preserved as in the extraction.
- No Lean compilation or formalization is claimed.
