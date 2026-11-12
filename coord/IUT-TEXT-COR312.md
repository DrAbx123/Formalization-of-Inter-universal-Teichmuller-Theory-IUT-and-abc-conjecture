# IUT-TEXT-COR312 — verbatim IUT III excerpts (A1037)

Source PDF: `papers/motizuki_corpus/raw/Inter-universal Teichmuller Theory III.pdf`.
Extraction: `tools/pdftotext_iut.py` -> `coord/IUT-TEXT/III.txt` (pypdf, page markers).
Quotes below are verbatim from the extracted text; page numbers are PDF page markers.

## 1. Corollary 3.12 (pp. 173-174)

> Corollary 3.12. (Log-volume Estimates for Θ-Pilot Objects) Suppose
> that we are in the situation of Theorem 3.11. Write
> −| log(Θ)|∈ R ⋃ {+∞}
> for the procession-normalized mono-analytic log-volume [i.e., where the av-
> erage is taken over j ∈ F⋇_l — cf. Remark 3.1.1, (ii), (iii), (iv); Proposition 3.9,
> (i), (ii); Theorem 3.11, (i), (a)] of the holomorphic hull [cf. Remark 3.9.5, (i)]
> of the union of the possible images of a Θ-pilot object [cf. Definition 3.8, (i)],
> relative to the relevant Kummer isomorphisms [cf. Theorem 3.11, (ii)], in the
> multiradial representation of Theorem 3.11, (i), which we regard as subject to
> the indeterminacies (Ind1), (Ind2), (Ind3) described in Theorem 3.11, (i), (ii).
> Write
> −| log(q)|∈ R
> for the procession-normalized mono-analytic log-volume of the image of a
> q-pilot object [cf. Definition 3.8, (i)], relative to the relevant Kummer isomor-
> phisms [cf. Theorem 3.11, (ii)], in the multiradial representation of Theorem
> 3.11, (i), which we do not regard as subject to the indeterminacies (Ind1), (Ind2),
> (Ind3) described in Theorem 3.11, (i), (ii). Here, we recall the definition of the
> symbol “∆” as the result of identifying the labels “0” and “⟨F⋇_l⟩”
> [cf. [IUTchII], Corollary 4.10, (i)]. In particular, |log(q)| > 0 is easily computed
> in terms of the various q-parameters of the elliptic curve E_F [cf. [IUTchI],
> Definition 3.1, (b)] at v ∈ V_bad (≠ ∅). Then it holds that −| log(Θ)|∈ R, and
> −| log(Θ)| ≥ −| log(q)|
> — i.e., C_Θ ≥ −1 for any real number C_Θ ∈ R such that −| log(Θ)| ≤ C_Θ · |log(q)|.

(PDF p. 173; statement continues to p. 174.)

## 2. Start of proof and the hull/union definitions (pp. 174-175)

> Proof. We begin by observing that, since |log(q)| > 0, we may assume without loss
> of generality in the remainder of the proof that
> −| log(Θ)| < 0
> whenever −| log(Θ)|∈ R [i.e., since an inequality −| log(Θ)|≥ 0 would imply
> that −| log(Θ)|≥ 0 > −|log(q)|]. Now suppose that we are in the situation of
> Theorem 3.11. For n ∈ Z, write
> n,◦U = { n,◦U_{j,vQ} }_{j∈|F_l|,vQ∈VQ} ⊆ n,◦UQ = { n,◦UQ_{j,vQ} }_{j∈|F_l|,vQ∈VQ}
> [where we observe that the “⊆” constitutes a slight abuse of notation] for the
> collection of subsets n,◦U_{j,vQ} ⊆ n,◦UQ_{j,vQ} = IQ(S±_{j+1}; n,◦D⊣_{vQ})
> [cf. Theorem 3.11, (i), (a)] given by the various unions, for j∈|F_l| and vQ∈VQ, of
> the possible images of a Θ-pilot object [cf. Definition 3.8, (i)], relative to the
> relevant Kummer isomorphisms [cf. Theorem 3.11, (ii)], in the multiradial
> representation of Theorem 3.11, (i), which we regard as subject to the
> indeterminacies (Ind1), (Ind2), (Ind3) described in Theorem 3.11, (i), (ii);
> n,◦U = { n,◦U_{j,vQ} } ⊆ n,◦UQ = { n,◦UQ_{j,vQ} }
> [where ...] for the collection of subsets ... given by the various holomorphic hulls
> [cf. Remark 3.9.5, (i)] of the subsets n,◦U_{j,vQ} ⊆ IQ(S±_{j+1}; n,◦D⊣_{vQ}),
> relative to the arithmetic holomorphic structure labeled “n,◦”. Here, we observe
> that one concludes easily from the [easily verified] compactness of the 1,◦U_{j,vQ}
> [where j∈|F_l|, vQ∈VQ], together with the definition of the log-volume, that the
> quantity −|log(Θ)| is finite, hence negative [by our assumption at the beginning
> of the present proof!].

(PDF pp. 174-175.)

## 3. The three indeterminacies (Theorem 3.11, pp. 153-156)

> Theorem 3.11. (Multiradial Algorithms via LGP-Monoids/Frobenioids)
> Fix a collection of initial Θ-data (F/F, X_F, l, C_K, V, V_bad_mod, ϵ) as in
> [IUTchI], Definition 3.1. ...
> (i) (Multiradial Representation) ... Write n,◦RLGP for the collection of data
> (a), (b), (c) regarded up to indeterminacies of the following two types:
> (Ind1) the indeterminacies induced by the automorphisms of the procession
> of D⊣-prime-strips Prc(n,◦D⊣_T);
> (Ind2) for each vQ ∈ V_non_Q (respectively, vQ ∈ V_arc_Q), the indeterminacies
> induced by the action of independent copies of I_sm [cf. Proposition 1.2, (vi)]
> (respectively, copies of each of the automorphisms of order 2 whose orbit
> constitutes the poly-automorphism discussed in Proposition 1.2, (vii)) on
> each of the direct summands of the j+1 factors appearing in the tensor
> product used to define IQ(S±_{j+1}; n,◦D⊣_{vQ}) [cf. (a) above; Proposition
> 3.2, (ii)] — where we recall that the cardinality of the collection of direct
> summands is equal to the cardinality of the set of v∈ V that lie over vQ.

(PDF pp. 153-154.)

> (Ind3) as one varies m ∈ Z, the isomorphisms of (a) are “upper semi-
> compatible”, relative to the log-links of the n-th column of the LGP-
> Gaussian log-theta-lattice under consideration, in a sense that involves
> certain natural inclusions “⊆” at vQ∈ V_non_Q and certain natural sur-
> jections “↠” at vQ∈ V_arc_Q — cf. Proposition 3.5, (ii), (a), (b), for more
> details.
> Finally, as one varies m∈ Z, the isomorphisms of (a) are [precisely!] compatible,
> relative to the log-links of the n-th column of the LGP-Gaussian log-theta-lattice
> under consideration, with the respective log-volumes [cf. Proposition 3.9, (iv)].

(PDF p. 156.)

## 4. Proof Step (x): log-volumes and indeterminacies (p. 181)

> (x) ... The theory of “Kummer-detachment” ... allows one to relate the
> Frobenioid-theoretic [i.e., “Frobenius-like”] structures that appear in the domain
> [i.e., at (0,0)] of the Θ×μ_LGP-link [cf. (i)] to the multiradial representation
> described in Theorem 3.11, (i), (a), (b), (c), but only at the cost of introducing
> the indeterminacies
> (Ind1) — which may be thought of as arising from the requirement of com-
> patibility with the permutation symmetries of the étale-picture [cf.
> Theorem 3.11, (i)];
> (Ind2) — which may be thought of as arising from the requirement of com-
> patibility with the Aut_{F⊣×μ}(−)-indeterminacies that act on the do-
> main/codomain of the Θ×μ_LGP-link [cf. (ii); Theorem 3.11, (i), (iii)], i.e.,
> with the horizontal arrows of the log-theta-lattice;
> (Ind3) — which may be thought of as arising from the requirement of compat-
> ibility with the log-Kummer correspondences of Theorem 3.11, (ii),
> i.e., with the vertical arrows of the log-theta-lattice.
> The various indeterminacies (Ind1), (Ind2), (Ind3) to which the multiradial repre-
> sentation is subject may be thought of as data that describes some sort of “formal
> quotient” ... In this context, the procession-normalized mono-analytic log-volumes
> [i.e., where the average is taken over j∈ F⋇_l] of Theorem 3.11, (i), (a), (c), furnish
> a means of constructing a sort of associated “coarse space” or “inductive limit”
> ... — i.e., in the sense that [one verifies immediately — cf. Proposition 3.9, (ii) —
> that] the resulting log-volumes ∈ R are invariant with respect to the indeterminacies
> (Ind1), (Ind2), and have the effect of converting the indeterminacy (Ind3) into an
> inequality [from above].

(PDF p. 181.)

## 5. Proof Step (xi): q-pilot and determinant/log-volume (pp. 181-183)

> (xi-a) Consider a q-pilot object at (1,0), which we think of — relative to the
> relevant copy of “F⊛_mod”— in terms of the holomorphic log-shells constructed
> at (1,0) ... Then the Θ×μ_LGP-link from (0,0) to (1,0) may be interpreted as a
> sort of gluing isomorphism that relates the arithmetic holomorphic structure ... at
> (1,0) to the arithmetic holomorphic structure at (0,0) in such a way that the
> Θ-pilot object at (0,0) ... corresponds to the q-pilot object at (1,0) ...
> (xi-c) ... The multiradial construction algorithm of Theorem 3.11 yields a collection
> of possibilities of output data in 1,◦U (⊆ 1,◦UQ) that are linked/related [cf. (IPL)],
> via isomorphisms of F⊩▶-prime-strips, to the representation [via the log-Kummer
> correspondence in the 1-column] of the q-pilot object at (1,0) on 1,◦UQ, and,
> moreover, whose construction may be expressed entirely relative to the arithmetic
> holomorphic structure in the 1-column [cf. (SHE)].
> (xi-d) ... it is only by forming [a suitable positive tensor power of] the determinant
> of the localizations of arithmetic vector bundles ... and then applying the
> [suitably normalized, with respect to j∈|F_l|] log-volume to various regions —
> i.e., the region 1,◦U and the region that arises from the representation of the q-pilot
> object at (1,0) on 1,◦UQ — in 1,◦UQ ... that we are able to obtain completely
> comparable objects ... namely,
> R_{≤−|log(Θ)|} := {λ∈ R | λ ≤ −| log(Θ)|} ⊆ R;  −| log(q)|∈ R
> — where we recall that, by definition, −|log(Θ)| is the [negative—cf. the discussion
> of “possible images” at the beginning of the present proof] log-volume of 1,◦U,
> while −| log(q)| is the log-volume of the region that arises from the representation
> of the q-pilot object at (1,0) on 1,◦UQ.

(PDF pp. 181-183.)

## 6. Remark 3.9.4: log-volumes and R>0 action (pp. 120-121)

> Remark 3.9.4. The log-link compatibility of log-volumes discussed in Propo-
> sition 3.9, (iv), may be formulated somewhat more explicitly by applying various
> elementary observations, as follows.
> (i) Let (M, μ_M) be a measure space [i.e., in the sense of the discussion of
> Remark 3.1.1, (iii)]. We shall say that a subset S ⊆ M is pre-ample if S is a
> relatively compact Borel set, that a pre-ample subset S ⊆ M is ample if μ_M(S) > 0,
> and that (M, μ_M) is ample if there exists an ample subset of M. ...
> Fn(M) [is] the set of Borel measurable functions f : M → R_{≥0} such that the image
> f(M) ⊆ R_{≥0} of f is a finite set ... Observe that Fn(M) is equipped with a
> natural monoid structure [induced by the natural monoid structure on R_{≥0}], as
> well as a natural action by R_{>0} [induced by the natural action by multiplication
> of R_{>0} on R_{≥0}]. ... integration over M, relative to the measure μ_M, determines
> an R_{>0}-equivariant surjection ∫_M : Fn(M) ↠ R_{≥0} ...

(PDF pp. 120-121.)

## 7. Notes for the formalization

- Cor 3.12 itself uses `−|log(q)|` and `−|log(Θ)|`; it does **not** spell out the
  `1/(2ℓ)` normalization.  The latter is in IUT IV, Theorem 1.10, p. 23:
  `|log(q)| = 1/(2l)·log(q)` (see `coord/IUT-TEXT-THM110.md`).
- The theta values are written `{q^{j²}}_{j=1,...,l⋇}` (Fig. 3.4, p. 172, and
  Theorem 3.11 discussion p. 159); the label set is `F⋇_l` and the average over
  `j∈F⋇_l` is the procession normalization.
- (Ind1) in Theorem 3.11 is stated as automorphisms of the procession of
  D⊣-prime-strips; the label-permutation reading comes from the `F⋊±_l` symmetry
  discussion, not from a separate bullet in the statement.
- (Ind3) is the upper semi-compatibility: inclusions `⊆` at nonarchimedean and
  surjections `↠` at archimedean; it is converted into an inequality from above
  by the log-volume (Step (x)).
