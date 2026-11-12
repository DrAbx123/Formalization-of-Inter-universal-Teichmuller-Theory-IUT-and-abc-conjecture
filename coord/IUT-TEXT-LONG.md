# IUT-TEXT-LONG - verbatim page ranges from IUT III/IV (A1039)

Source: `coord/IUT-TEXT/III.txt` and `coord/IUT-TEXT/IV.txt`, produced by
`tools/pdftotext_iut.py` (pypdf) from the IUT PDFs.  Each page block below is the
raw extracted text for that PDF page; line breaks/OCR artifacts are preserved.

Page index:
- IUT III - Theorem 3.11 and indeterminacies (pp. 150-160): 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160
- IUT III - Corollary 3.12 proof, Steps (x)-(xi) (pp. 181-183): 181, 182, 183
- IUT IV - Theorem 1.10 normalization (pp. 22-23): 22, 23
- IUT IV - Theorem 1.10 proof, Steps (iv)-(v) (pp. 27-29): 27, 28, 29

## IUT III - Theorem 3.11 and indeterminacies (pp. 150-160)

### Page 150

```text
150 SHINICHI MOCHIZUKI
Proposition 3.7, (ii)]. These local monoids are subject to a somewhat more compli-
cated “log-Kummer correspondence” [cf. Proposition 3.5, (ii)] that revolves around
“upper semi-compatibility”, i.e., in a word,one-sided inclusions, as opposed to pre-
cise equalities. The imprecise nature of such one-sided inclusions isincompatible
with the construction of “(†F⊛
mod)α”. In particular, one cannot constructlog-link-
compatible isomorphisms of Frobenioids for “(†F⊛
mod)α” as in the ﬁrst display of
Proposition 3.10, (iii).
(ii) The precise compatibility of “F⊛
MOD”w i t ht h elog-links of the LGP-
Gaussian log-theta-lattice [cf. the discussion of (i); the ﬁrst “mutual compatibil-
ity” of Proposition 3.10, (iii)] makes it more suited [i.e., by comparison to “F⊛
mod”]
to the task of computing theKummer-detachment indeterminacies [cf. Re-
mark 1.5.4, (i), (iii)] that arise when one attempts to pass from theFrobenius-like
structures constituted by the global portion of the domain of the Θ×μ
LGP-links of the
LGP-Gaussian log-theta-lattice to corresponding´etale-like structures.T h a t i s t o
say, the mutual compatibility of the isomorphisms
n,mF⊩⊥
LGP
∼
→ F⊩⊥(n,◦HT D-Θ±ellNF)LGP
of the second display of Proposition 3.10, (iii), asserts, in eﬀect, that suchKummer-
detachment indeterminacies do not arise. This is precisely the reason why we
wish to work with the LGP-, as opposed to thelgp-, Gaussian log-theta lattice
[cf. Remark 3.8.1]. On the other hand, the essentiallymultiplicative nature of
“F⊛
MOD” [cf. Remark 3.6.2, (ii)] makes itill-suited to the task of computing the
´etale-transport indeterminacies [cf. Remark 1.5.4, (i), (ii)] that occur as one
passes between distinct arithmetic holomorphic structures on opposite sides of a
Θ×μ
LGP-link.
(iii) By contrast, whereas theadditive natureof the local modules [i.e., local
fractional ideals] that occur in the construction of “F⊛
mod” renders “F⊛
mod” ill-suited
to the computation of Kummer-detachment indeterminacies [cf. the discussion of
(i), (ii)], theclose relationship[cf. Proposition 3.9, (i), (ii), (iii)] of these local mod-
ules to themono-analytic log-shellsthat arecoric with respect to the Θ×μ
LGP-link
[cf. Theorem 1.5, (iv); Remark 3.8.2] renders “F⊛
mod” well-suited to the computa-
tion of the´etale-transport indeterminacies that occur as one passes between
distinct arithmetic holomorphic structures on opposite sides of a Θ×μ
LGP-link. That
is to say, although variousdistortions of these local modules arise as a result of both
[the Kummer-detachment indeterminacies constituted by] the local“upper semi-
compatibility” of Proposition 3.5, (ii), and [the ´etale-transport indeterminacies
constitutedby]the discrepancy betweenlocal holomorphicand mono-analytic
integral structures[cf. Remark 3.9.1, (i), (ii)], one may nevertheless compute —
i.e., if one takes into account the various distortions that occur,“estimate” —
the global arithmetic degreesof objects of “F⊛
mod” by computinglog-volumes
[cf. Proposition 3.9, (iii)], which arebi-coric, i.e., coric with respect to both the
Θ×μ
LGP-links [cf. Proposition 3.9, (ii)] and thelog-links [cf. Proposition 3.9, (iv)] of
the LGP-Gaussian log-theta-lattice. Thiscomputability is precisely the topic of
Corollary 3.12 below. On the other hand, the issue of obtainingconcrete estimates
will be treated in [IUTchIV].
```

### Page 151

```text
INTER-UNIVERSAL TEICHM¨ULLER THEORY III 151
F⊛
MOD/LGP-structures F⊛
mod/lgp-structures
biased toward biased toward
multiplicative structures additive structures
easily related to easily related tounit group/coric
value group/non-coricportion portion “(−)⊣×μ”o fΘ×μ
LGP-/Θ×μ
lgp-link,
“(−)⊩▶”o fΘ×μ
LGP-link i.e., mono-analytic log-shells
admits only admits
precise log-Kummer “upper semi-compatible”
correspondence log-Kummer correspondence
rigid, but not suited subject tosubstantial distortion,
to explicit computation but suited toexplicit estimates
Fig. 3.2:F⊛
MOD/LGP-structures versusF⊛
mod/lgp-structures
(iv) The various properties of “F⊛
MOD”a n d“F⊛
mod” discussed in (i), (ii), (iii)
above are summarized in Fig. 3.2 above. In this context, it is of interest to observe
that the natural isomorphisms of Frobenioids
F⊛
mod(n,◦HT D-Θ±ellNF)α
∼
→F ⊛
MOD(n,◦HT D-Θ±ellNF)α
as well as the resulting isomorphisms ofF⊩-prime-strips
F⊩(n,◦HT D-Θ±ellNF)LGP
∼
→ F⊩(n,◦HT D-Θ±ellNF)lgp
of Proposition 3.10, (i), play thehighly nontrivialrole of relating [cf. the discussion
of [IUTchII], Remark 4.8.2, (i)] the “multiplicatively biasedF⊛
MOD”t ot h e“addi-
tively biasedF⊛
mod” by means of theglobal ring structure of the number ﬁeld
M
⊛
mod(n,◦HT D-Θ±ellNF)α = M
⊛
MOD(n,◦HT D-Θ±ellNF)α. A similar statement holds
concerning the tautological isomorphism ofF⊩-prime-strips †F⊩
LGP
∼
→ †F⊩
lgp of
Proposition 3.7, (iv).
Remark 3.10.2. In the context of the variousKummer isomorphismsdiscussed
in the ﬁnal display of Proposition 3.10, (i), it is useful to recall that theF⊩▶×μ-
prime-strips †F⊩▶×μ
LGP , †F⊩▶×μ
lgp that appear in the deﬁnition of the Θ×μ
LGP-, Θ×μ
lgp-
links in Deﬁnition 3.8, (ii), were constructed from theF⊩▶×μ-prime-strip †F⊩▶×μ
env
[associated to the F⊩-prime-strip †F⊩
env] of [IUTchII], Corollary 4.10, (ii), in a
```

### Page 152

```text
152 SHINICHI MOCHIZUKI
fashion that we review as follows. First, we remark that, in the present discussion,
it is convenient for us to think of ourselves as working with objects arising from
the LGP-Gaussian log-theta-latticeof Deﬁnition 3.8, (iii) [so “†” will be replaced by
“(n,m)” or “(n,◦)”]. Now recall, from the theory developed so far in the present
series of papers, that we have acommutative diagram ofF⊩▶×μ-prime-strips
F⊩▶×μ(n,◦)env
∼
→ F⊩▶×μ(n,◦)gau
∼
→ F⊩▶×μ(n,◦)LGP
∼
→ F⊩▶×μ(n,◦)lgp
↑⏐
⏐
↑⏐
⏐
↑⏐
⏐
↑⏐
⏐
n,mF⊩▶×μ
env
∼
→ n,mF⊩▶×μ
gau
∼
→ n,mF⊩▶×μ
LGP
∼
→ n,mF⊩▶×μ
lgp
—w h e r e
· for simplicity, we use the abbreviated version “n,◦” of the notation
“n,◦HT D-Θ±ellNF” of Proposition 3.10, (i);
· the ﬁrst vertical arrow is the inducedF⊩▶×μ-prime-strip version of
the Kummer isomorphism[whose codomain includes an argument “†D>”,
which we denote here by “n,◦”] of the ﬁnal display of Proposition 2.1, (ii)
[cf. also Proposition 2.1, (iii), (iv), (v)];
· the second, third, and fourth vertical arrowsare the inducedF⊩▶×μ-
prime-strip versions of theKummer isomorphisms of the ﬁnal display of
Proposition 3.10, (i);
· theﬁrst lower horizontal arrowis the inducedF⊩▶×μ-prime-strip version
of theevaluation isomorphismof the ﬁnal display of [IUTchII], Corollary
4.10, (ii);
· the second and third lower horizontal arrowsare the inducedF⊩▶×μ-
prime-strip versions of thetautological isomorphismsof the ﬁnal displays
of Proposition 3.7, (iii), (iv);
· theﬁrst upper horizontal arrowis the inducedF⊩▶×μ-prime-strip version
of the´etale-like evaluation isomorphismimplicit in the construction [via
[IUTchII], Corollary 4.6, (iv), (v)] of the evaluation isomorphism of the
ﬁnal display of [IUTchII], Corollary 4.10, (ii);
· the second and third upper horizontal arrowsare the inducedF⊩▶×μ-
prime-strip versions of thenatural isomorphismsof the second display of
Proposition 3.10, (i).
That is to say, in summary,
theF⊩▶×μ-prime-strips n,mF⊩▶×μ
LGP , n,mF⊩▶×μ
lgp that appear in the Θ×μ
LGP-,
Θ×μ
lgp-links of Deﬁnition 3.8, (iii), wereconstructed from theF⊩▶×μ-prime-
strip n,mF⊩▶×μ
env and related to thisF⊩▶×μ-prime-strip n,mF⊩▶×μ
env via the
lowerhorizontalarrowsoftheabovecommutativediagram; moreover, each
of these lower horizontal arrowsmay be constructed byconjugating the
corresponding upper horizontal arrowby the relevant Kummer isomor-
phisms, i.e., by thevertical arrowsin the diagram.
```

### Page 153

```text
INTER-UNIVERSAL TEICHM¨ULLER THEORY III 153
We are now ready to discuss themain theoremof the present series of papers.
Theorem 3.11. (Multiradial Algorithms via LGP-Monoids/Frobenioids)
Fix a collection ofinitial Θ-data
(F/F, XF,l ,C K, V, Vbad
mod,ϵ)
as in [IUTchI], Deﬁnition 3.1. Let
{n,mHT Θ±ellNF}n,m∈Z
be acollection of distinctΘ±ellNF-Hodge theaters[relative to the given initial
Θ-data] — which we think of as arising from anLGP-Gaussian log-theta-lattice
[cf. Deﬁnition 3.8, (iii)]. For eachn∈ Z, write
n,◦HT D-Θ±ellNF
for theD-Θ±ellNF-Hodge theater determined, up to isomorphism, by the various
n,mHT Θ±ellNF,w h e r em∈ Z,v i at h evertical coricity of Theorem 1.5, (i) [cf.
Remark 3.8.2].
(i) (Multiradial Representation)Consider theprocession ofD⊣-prime-
strips Prc(n,◦D⊣
T)
{n,◦D⊣
0} ↪→{ n,◦D⊣
0, n,◦D⊣
1} ↪→ ... ↪→{ n,◦D⊣
0, n,◦D⊣
1,. . . ,n,◦D⊣
l⋇}
obtained by applying the natural functor of [IUTchI], Proposition 6.9, (ii), to [the
D-Θ±-bridge associated to]n,◦HT D-Θ±ellNF. Consider also the following data:
(a) for V∋v| vQ ∈ VQ, j∈| Fl|,t h etopological modules and mono-
analytic integral structures
I(S±
j+1;n,◦D⊣
vQ) ⊆I Q(S±
j+1;n,◦D⊣
vQ); I(S±
j+1,j;n,◦D⊣
v) ⊆I Q(S±
j+1,j;n,◦D⊣
v)
— where the notation “;n,◦” denotes the result of applying the construc-
tion in question to the case ofD⊣-prime-strips labeled “n,◦” — of Proposi-
tion 3.2, (ii) [cf. also the notational conventions of Proposition 3.4, (ii)],
which we regard as equipped with theprocession-normalized mono-
analytic log-volumesof Proposition 3.9, (ii);
(b) for Vbad∋v,t h esplitting monoid
Ψ⊥
LGP(n,◦HT D-Θ±ellNF)v
of Proposition 3.5, (ii), (c) [cf. also the notation of Proposition 3.5, (i)],
which we regard — via the natural poly-isomorphisms
IQ(S±
j+1,j;n,◦D⊣
v)
∼
→I Q(S±
j+1,jF⊣×μ(n,◦D≻)v)
∼
→I Q(S±
j+1,jF(n,◦D≻)v)
```

### Page 154

```text
154 SHINICHI MOCHIZUKI
for j∈ F⋇
l [cf. Proposition 3.2, (i), (ii)] — as asubset of
∏
j∈F⋇
l
IQ(S±
j+1,j;n,◦D⊣
v)
equipped with a(n) [multiplicative]action on ∏
j∈F⋇
l
IQ(S±
j+1,j;n,◦D⊣
v);
(c) for j∈ F⋇
l ,t h enumber ﬁeld
M
⊛
MOD(n,◦HT D-Θ±ellNF)j = M
⊛
mod(n,◦HT D-Θ±ellNF)j
⊆I Q(S±
j+1;n,◦D⊣
VQ)
def
=
∏
vQ∈VQ
IQ(S±
j+1;n,◦D⊣
vQ)
[cf. the natural poly-isomorphisms discussed in (b); Proposition 3.9, (iii);
Proposition 3.10, (i)], together withnatural isomorphismsbetween the
associated global non-realiﬁed/realiﬁed Frobenioids
F⊛
MOD(n,◦HT D-Θ±ellNF)j
∼
→F ⊛
mod(n,◦HT D-Θ±ellNF)j
F⊛R
MOD(n,◦HT D-Θ±ellNF)j
∼
→F ⊛R
mod(n,◦HT D-Θ±ellNF)j
[cf. Proposition 3.10, (i)], whose associated “global degrees” may be
computed by means of thelog-volumes of (a) [cf. Proposition 3.9, (iii)].
Write
n,◦RLGP
for the collection of data (a), (b), (c) regarded up toindeterminacies of the
following two types:
(Ind1) the indeterminacies induced by theautomorphisms of theprocession
ofD⊣-prime-strips Prc(n,◦D⊣
T);
(Ind2) for eachvQ∈ Vnon
Q (respectively,vQ∈ Varc
Q ), the indeterminacies induced
by the action of independent copies of Ism [cf. Proposition 1.2, (vi)]
(respectively, copies of each of the automorphisms of order2 whose orbit
constitutes the poly-automorphism discussed in Proposition 1.2, (vii)) on
each of thedirect summandsof thej+1 factors appearing in the tensor
product used to deﬁneIQ(S±
j+1;n,◦D⊣
vQ) [cf. (a) above; Proposition 3.2, (ii)]
— where we recall that the cardinality of the collection of direct summands
is equal to the cardinality of the set ofv∈ V that lie overvQ.
Then n,◦RLGP may be constructed via analgorithm in the procession ofD⊣-prime-
strips Prc(n,◦D⊣
T) that is functorial with respect to isomorphisms of processions
ofD⊣-prime-strips. For n,n′∈ Z,t h epermutation symmetries of the ´etale-
picture discussed in [IUTchI], Corollary 6.10, (iii); [IUTchII], Corollary 4.11, (ii),
(iii) [cf. also Corollary 2.3, (ii); Remarks 2.3.2 and 3.8.2, of the present paper],
induce compatible poly-isomorphisms
Prc(n,◦D⊣
T)
∼
→ Prc(n′,◦D⊣
T); n,◦RLGP ∼
→ n′,◦RLGP
```

### Page 155

```text
INTER-UNIVERSAL TEICHM¨ULLER THEORY III 155
which are, moreover, compatible with the poly-isomorphisms
n,◦D⊣
0
∼
→ n′,◦D⊣
0
induced by thebi-coricitypoly-isomorphisms of Theorem 1.5, (iii) [cf. also [IUTchII],
Corollaries 4.10, (iv); 4.11, (i)].
(ii) (log-Kummer Correspondence)For n,m∈ Z,t h eKummer isomor-
phisms of labeled data
Ψcns(n,mF≻)t
∼
→ Ψcns(n,◦D≻)t
{πκ-sol
1 (n,mD⊛) ↷ n,mM⊛
∞κ}j
∼
→{ πκ-sol
1 (n,◦D⊛) ↷M ⊛
∞κ(n,◦D⊚)}j
(n,mM
⊛
mod)j
∼
→ M
⊛
mod(n,◦D⊚)j
—w h e r et∈ LabCusp±(n,◦D≻) — of [IUTchII], Corollary 4.6, (iii); [IUTchII],
Corollary 4.8, (i), (ii) [cf. also Propositions 3.5, (i); 3.10, (i), of the present
paper] induceisomorphisms between the vertically coric data (a), (b), (c) of
(i) [which we regard, in the present (ii), as data which hasnot yetbeen subjected
to the indeterminacies(Ind1), (Ind2) discussed in (i)] and the corresponding data
arising from eachΘ±ellNF-Hodge theatern,mHT Θ±ellNF, i.e.:
(a) for V ∋v | vQ, j ∈| Fl|, isomorphisms with local mono-analytic
tensor packetsand theirQ-spans
I(S±
j+1;n,mFvQ)
∼
→I (S±
j+1;n,mF⊣×μ
vQ )
∼
→I (S±
j+1;n,◦D⊣
vQ)
IQ(S±
j+1;n,mFvQ)
∼
→I Q(S±
j+1;n,mF⊣×μ
vQ )
∼
→I Q(S±
j+1;n,◦D⊣
vQ)
I(S±
j+1,j;n,mFv)
∼
→I (S±
j+1,j;n,mF⊣×μ
v )
∼
→I (S±
j+1,j;n,◦D⊣
v)
IQ(S±
j+1,j;n,mFv)
∼
→I Q(S±
j+1,j;n,mF⊣×μ
v )
∼
→I Q(S±
j+1,j;n,◦D⊣
v)
[cf. Propositions 3.2, (i), (ii); 3.4, (ii); 3.5, (i)], all of which arecom-
patible with the respectivelog-volumes [cf. Proposition 3.9, (ii)];
(b) for Vbad∋v, isomorphisms ofsplitting monoids
Ψ⊥
FLGP(n,mHT Θ±ellNF)v
∼
→ Ψ⊥
LGP(n,◦HT D-Θ±ellNF)v
[cf. Proposition 3.5, (i); Proposition 3.5, (ii), (c)];
(c) for j∈ F⋇
l , isomorphisms ofnumber ﬁeldsand global non-realiﬁed/
realiﬁed Frobenioids
(n,mM
⊛
MOD)j
∼
→ M
⊛
MOD(n,◦HT D-Θ±ellNF)j;( n,mM
⊛
mod)j
∼
→ M
⊛
mod(n,◦HT D-Θ±ellNF)j
(n,mF⊛
MOD)j
∼
→F ⊛
MOD(n,◦HT D-Θ±ellNF)j;( n,mF⊛
mod)j
∼
→F ⊛
mod(n,◦HT D-Θ±ellNF)j
(n,mF⊛R
MOD)j
∼
→F ⊛R
MOD(n,◦HT D-Θ±ellNF)j;( n,mF⊛R
mod)j
∼
→F ⊛R
mod(n,◦HT D-Θ±ellNF)j
```

### Page 156

```text
156 SHINICHI MOCHIZUKI
which are compatible with the respective natural isomorphisms between
“MOD”- and “mod”-subscripted versions [cf. Proposition 3.10, (i)]; here,
the isomorphisms of the third line of the display induce isomorphisms of
the global realiﬁed Frobenioidportions
n,mC⊩
LGP
∼
→C ⊩
LGP(n,◦HT D-Θ±ellNF); n,mC⊩
lgp
∼
→C ⊩
lgp(n,◦HT D-Θ±ellNF)
of theF⊩-prime-strips n,mF⊩
LGP, F⊩(n,◦HT D-Θ±ellNF)LGP, n,mF⊩
lgp,a n d
F⊩(n,◦HT D-Θ±ellNF)lgp [cf. Propositions 3.7, (iii), (iv), (v); 3.10, (i)].
Moreover, as one variesm∈ Z, the various isomorphisms of (b) and of the ﬁrst
line in the ﬁrst display of (c) aremutually compatiblewith one another, relative
to the log-links of the n-th column of the LGP-Gaussian log-theta-lattice under
consideration, in the sense that the only portions of the domains of these isomor-
phisms that are possibly related to one another via thelog-links consist ofroots of
unity in the domains of thelog-links [multiplication by which corresponds, via the
log-link, to an“addition by zero”indeterminacy, i.e., tono indeterminacy!]
— cf. Proposition 3.5, (ii), (c); Proposition 3.10, (ii). This mutual compatibility of
the isomorphisms of the ﬁrst line in the ﬁrst display of (c) implies a corresponding
mutual compatibilitybetween the isomorphisms of the second and third lines in
the ﬁrst display of (c) thatinvolve the subscript “MOD” [but not between the
isomorphisms that involve the subscript “mod”! — cf. Proposition 3.10, (iii); Re-
mark 3.10.1]. On the other hand, the isomorphisms of (a) are subject to a certain
“indeterminacy” as follows:
(Ind3) as one varies m ∈ Z, the isomorphisms of (a) are “upper semi-
compatible”, relative to the log-links of the n-th column of theLGP-
Gaussian log-theta-lattice under consideration, in a sense that involves
certain natural inclusions “⊆” at vQ∈ Vnon
Q and certainnatural sur-
jections “↠” at vQ∈ Varc
Q — cf. Proposition 3.5, (ii), (a), (b), for more
details.
Finally, as one variesm∈ Z, the isomorphisms of (a) are [precisely!]compatible,
relative to the log-links of the n-th column of theLGP-Gaussian log-theta-lattice
under consideration, with the respectivelog-volumes [cf. Proposition 3.9, (iv)].
(iii) (Θ×μ
LGP-Link Compatibility)The various Kummer isomorphisms of (ii)
satisfy compatibility properties with the varioushorizontal arrows— i.e.,Θ×μ
LGP-
links — of theLGP-Gaussian log-theta-lattice under consideration as follows:
(a) The ﬁrst Kummer isomorphism of the ﬁrst display of (ii) induces — by
applying theF⋊±
l -symmetry of theΘ±ellNF-Hodge theatern,mHT Θ±ellNF
—a Kummer isomorphism n,mF⊣×μ
∆
∼
→ F⊣×μ
∆ (n,◦D⊣
∆) [cf. The-
orem 1.5, (iii)]. Relative to this Kummer isomorphism, the full poly-
isomorphism ofF⊣×μ-prime-strips
F⊣×μ
∆ (n,◦D⊣
∆)
∼
→ F⊣×μ
∆ (n+1,◦D⊣
∆)
is compatible with the full poly-isomorphism ofF⊣×μ-prime-strips
n,mF⊣×μ
∆
∼
→ n+1,mF⊣×μ
∆
```

### Page 157

```text
INTER-UNIVERSAL TEICHM¨ULLER THEORY III 157
induced [cf. Theorem 1.5, (ii)] by thehorizontal arrows of the LGP-
Gaussian log-theta-lattice under consideration [cf. Theorem 1.5, (iii)].
(b) TheF⊩-prime-strips n,mF⊩
env, F⊩
env(n,◦D>) [cf. Proposition 2.1, (ii)] that
appear implicitly in the construction of theF⊩-prime-strips n,mF⊩
LGP,
F⊩(n,◦HT D-Θ±ellNF)LGP, n,mF⊩
lgp, F⊩(n,◦HT D-Θ±ellNF)lgp [cf. (ii), (b),
(c), above; Proposition 3.4, (ii); Proposition 3.7, (iii), (iv); [IUTchII],
Corollary 4.6, (iv), (v); [IUTchII], Corollary 4.10, (ii)] admitnatural
isomorphisms of associatedF⊣×μ-prime-strips n,mF⊣×μ
∆
∼
→ n,mF⊣×μ
env ,
F⊣×μ
∆ (n,◦D⊣
∆)
∼
→ F⊣×μ
env (n,◦D>) [cf. Proposition 2.1, (vi)]. Relative to
these natural isomorphisms and to the Kummer isomorphism discussed in
(a) above, the full poly-isomorphism ofF⊣×μ-prime-strips
F⊣×μ
env (n,◦D>)
∼
→ F⊣×μ
env (n+1,◦D>)
is compatible with the full poly-isomorphism ofF⊣×μ-prime-strips
n,mF⊣×μ
∆
∼
→ n+1,mF⊣×μ
∆
induced [cf. Theorem 1.5, (ii)] by thehorizontal arrows of the LGP-
Gaussian log-theta-lattice under consideration [cf. Corollary 2.3, (iii)].
(c) Recall the data “ n,◦R” [cf. Corollary 2.3, (ii)] associated to the D-
Θ±ellNF-Hodge theatern,◦HT D-Θ±ellNF — data which appearsimplicitly
in the construction of theF⊩-prime-strips n,mF⊩
LGP, F⊩(n,◦HT D-Θ±ellNF)LGP,
n,mF⊩
lgp, F⊩(n,◦HT D-Θ±ellNF)lgp [cf. (ii), (b), (c), above; Proposition
3.4, (ii); Proposition 3.7, (iii), (iv); [IUTchII], Corollary 4.6, (iv), (v);
[IUTchII], Corollary 4.10, (ii)]. This data that arises fromn,◦HT D-Θ±ellNF
is related to corresponding data that arises from the projective system of
mono-theta environments associated to the tempered Frobenioids of the
Θ±ellNF-Hodge theater n,mHT Θ±ellNF at v ∈ Vbad via the Kummer
isomorphisms and poly-isomorphisms of projective systems of
mono-theta environments discussed in Proposition 2.1, (ii), (iii) [cf.
also Proposition 2.1, (vi); the second display of Theorem 2.2, (ii)] and
Theorem 1.5, (iii) [cf. also (a), (b) above], (v). Thealgorithmic con-
struction of these Kummer isomorphisms and poly-isomorphisms of pro-
jective systems of mono-theta environments, as well as of the poly-isomor-
phism
n,◦R
∼
→ n+1,◦R
induced by anypermutation symmetryof the´etale-picture [cf. the ﬁ-
nal portion of (i) above; Corollary 2.3, (ii); Remark 3.8.2]n,◦HT D-Θ±ellNF
∼
→ n+1,◦HT D-Θ±ellNF is compatible with the horizontal arrows of
the LGP-Gaussian log-theta-lattice under consideration, e.g., with the full
poly-isomorphism ofF⊣×μ-prime-strips
n,mF⊣×μ
∆
∼
→ n+1,mF⊣×μ
∆
```

### Page 158

```text
158 SHINICHI MOCHIZUKI
induced [cf. Theorem 1.5, (ii)] by these horizontal arrows [cf. Corollary
2.3, (iv)], in the sense that these constructions arestabilized/equivari-
ant/functorial with respect to arbitrary automomorphisms of the domain
and codomain of these horizontal arrows of theLGP-Gaussian log-theta-
lattice. Finally, thealgorithmic constructionof the poly-isomorphisms
of the ﬁrst display above, the various related Kummer isomorphisms, and
the variousevaluation maps implicit in the portion of thelog-Kummer
correspondence discussed in (ii), (b), arecompatible with the hori-
zontal arrowsof theLGP-Gaussian log-theta-lattice under consideration,
i.e., up to the indeterminacies(Ind1), (Ind2), (Ind3) described in (i), (ii)
[cf. also the discussion of Remark 3.11.4 below], in the sense that these
constructions arestabilized/equivariant/functorialwith respect to ar-
bitrary automomorphisms of the domain and codomain of these horizontal
arrows of theLGP-Gaussian log-theta-lattice.
(d) The algorithmic construction of the Kummer isomorphisms of the
ﬁrst display of (ii) [cf. also (a), (b) above; the gluing discussed in
[IUTchII], Corollary 4.6, (iv); the Kummer compatibilities discussed in
[IUTchII], Corollary 4.8, (iii); the relationship to the notation of [IUTchI],
Deﬁnition 5.2, (vi), (viii), referred to in [IUTchII], Propositions 4.2, (i),
and 4.4, (i)], as well as of the poly-isomorphisms between the data
[{πκ-sol
1 (n,◦D⊛) ↷M ⊛
∞κ(n,◦D⊚)}j
→ M∞κv(n,◦Dvj ) ⊆ M∞κ×v(n,◦Dvj )
]
v∈V
∼
→
[{πκ-sol
1 (n+1,◦D⊛) ↷M ⊛
∞κ(n+1,◦D⊚)}j
→ M∞κv(n+1,◦Dvj
) ⊆ M∞κ×v(n+1,◦Dvj
)
]
v∈V
[i.e., of the second line of the ﬁrst display of [IUTchII], Corollary 4.7, (iii)]
induced by anypermutation symmetryof the´etale-picture [cf. the ﬁ-
nal portion of (i) above; Corollary 2.3, (ii); Remark 3.8.2]n,◦HT D-Θ±ellNF
∼
→ n+1,◦HT D-Θ±ellNF are compatible [cf. the discussion of Remark
2.3.2] with the full poly-isomorphism ofF⊣×μ-prime-strips
n,mF⊣×μ
∆
∼
→ n+1,mF⊣×μ
∆
induced [cf. Theorem 1.5, (ii)] by thehorizontal arrows of the LGP-
Gaussian log-theta-lattice under consideration, in the sense that these con-
structions are stabilized/equivariant/functorial with respect to arbi-
trary automomorphisms of the domain and codomain of these horizon-
tal arrows of theLGP-Gaussian log-theta-lattice. Finally, the algorith-
mic construction of the poly-isomorphisms of the ﬁrst display above,
the various related Kummer isomorphisms, and the variousevaluation
maps implicit in the portion of thelog-Kummer correspondence dis-
cussed in (ii), (c), arecompatible with the horizontal arrows of the
LGP-Gaussian log-theta-lattice under consideration, i.e., up to the inde-
terminacies (Ind1), (Ind2), (Ind3) described in (i), (ii) [cf. also the dis-
cussion of Remark 3.11.4 below], in the sense that these constructions
```

### Page 159

```text
INTER-UNIVERSAL TEICHM¨ULLER THEORY III 159
are stabilized/equivariant/functorial with respect to arbitrary auto-
momorphisms of the domain and codomain of these horizontal arrows of
the LGP-Gaussian log-theta-lattice.
Proof. The various assertions of Theorem 3.11 follow immediately from the deﬁ-
nitions and the references quoted in the statements of these assertions — cf. also
the various related observations of Remarks 3.11.1, 3.11.2, 3.11.3, 3.11.4 below.©
Remark 3.11.1.
(i) One way to summarize the content of Theorem 3.11 is as follows:
Theorem 3.11 gives analgorithm for describing, up to certain relatively
mild indeterminacies,t h eLGP-monoids [cf. Fig. 3.1] — i.e., in
essence, thetheta values
{
qj2 }
j=1,...,l⋇
— which are constructed relative to thescheme/ring structure, i.e.,
“arithmetic holomorphic structure”, associated toone vertical line
[i.e., “(n,◦)” for someﬁxed n∈ Z] in the LGP-Gaussian log-theta-lattice
under consideration, in terms of thea priorialien arithmetic holomorphic
structure ofanother vertical line [i.e., “(n+1,◦)”] in the LGP-Gaussian
log-theta-lattice under consideration [cf., especially, the ﬁnal portion of
Theorem 3.11, (i), concerning functoriality and compatibility with the
permutation symmetriesof the´etale-picture].
This point of view is consistent with the point of view of the discussion of Remark
1.5.4; [IUTchII], Remark 3.8.3, (iii).
(ii) Although the various versions of the Θ-link are deﬁned [cf. Deﬁnition 3.8,
(ii)] asgluings of
theF⊩▶×μ-prime-strip whose associated pilot object [cf. [IUTchII], Deﬁ-
nition 4.9, (viii)] is some sort of Θ-pilot objectin thedomain of the Θ-link
to
theF⊩▶×μ-prime-stripwhoseassociatedpilotobjectissomesortof q-pilot
object in thecodomainof the Θ-link,
in fact it is not diﬃcult to see that the theory developed in the present series of
papers remainsessentially unaﬀected
even if onereplaces this q-pilotF⊩▶×μ-prime-strip in thecodomain of
the Θ-link by some otherF⊩▶×μ-prime-strip
such as, for instance, theF⊩▶×μ-prime-strip whose associated pilot object is the
qλ-pilot object[i.e., the λ-th power of theq-pilot object, for some positive integer
λ> 1] — cf. the discussion of Remark 3.12.1, (ii), below. One way to formulate this
observation is as follows: The Θ-link compatibilitydescribed in Theorem 3.11, (iii),
may be interpreted as an assertion to the eﬀect that thefunctorial construction
```

### Page 160

```text
160 SHINICHI MOCHIZUKI
algorithm for the Θ-pilot object up to certainmild indeterminacies [i.e., (Ind1),
(Ind2), (Ind3)] that is given in Theorem 3.11 may be regarded as
an algorithm whose input data is an F⊩▶×μ-prime-strip [i.e., the
F⊩▶×μ-prime-stripthatappearsinthe codomain of theΘ-link], andwhose
functorialityiswithrespectto arbitrary isomorphismsoftheF⊩▶×μ-
prime-strips that appear as input data of the algorithm.
From the point of view of thegluing given by the Θ-link,t h i sfunctoriality in the
input datagiven by anF⊩▶×μ-prime-strip may be interpreted in the following way:
this functoriality allows one to regard thefunctorial construction al-
gorithm for the Θ-pilot objectup to certainmild indeterminaciesthat is
given in Theorem 3.11 as an algorithm with respect to which thecodomain
Θ±ellNF-Hodge theater of the Θ-link [together with the other Θ±ellNF-
Hodge theaters in the same vertical line of the log-theta-lattice as this
codomain Θ±ellNF-Hodge theater] — i.e., in eﬀect, theq-pilotF⊩▶×μ-
prime-strip, equipped with therigidiﬁcation determined by thearith-
metic holomorphic structureconstitutedbythis vertical lineofΘ±ellNF-
Hodgetheaters—is “coric”, i.e., “remainsinvariant”/“mayberegarded
as being heldﬁxed” throughout the execution of the various operations
of the algorithm.
This interpretation will play acrucial role in the application of Theorem 3.11 to
Corollary 3.12 below.
(iii) On the other hand, the´etale-picture permutation symmetries dis-
cussed in the ﬁnal portion of Theorem 3.11, (i) [cf. also the references to these
symmetries in Theorem 3.11, (iii), (c), (d)], may be interpreted as follows: The
output data of the functorial construction algorithm of Theorem 3.11 con-
sists of a representation of the data of Theorem 3.11, (i), (b), (c) [cf. also Theorem
3.11, (iii), (c), (d)], up to certainmild indeterminacieson themono-analytic ´etale-
like log-shellsof Theorem 3.11, (i), (a), that satisﬁes the followingproperties:
· (Input prime-strip link (IPL)) This output data is constructed
in such a way that it islinked/related, via full poly-isomorphisms of
F⊩▶×μ-prime-strips induced by operations in the algorithm, to the
input data prime-strip, i.e., the “coric”/“ﬁxed” q-pilot F⊩▶×μ-
prime-strip, equipped with its rigidifying arithmetic holomorphic
structure [cf. the discussion of (ii)]. In particular, we note thateach of
these “intermediate”F⊩▶×μ-prime-strips that appears in the construc-
tion mayitself be taken to beboth
the input data of thefunctorial algorithm of Theorem 3.11
[cf. the discussion of (ii)]
and
[by applying the full poly-isomorphisms ofF⊩▶×μ-prime-strips
that link/relate it to theq-pilotF⊩▶×μ-prime-strip] the input
data for theKummer theorysurrounding the q-pilot object
F⊩▶×μ-prime-strip in its rigidifying Θ±ellNF-Hodge theater
[cf. the discussion of (ii)].
```

## IUT III - Corollary 3.12 proof, Steps (x)-(xi) (pp. 181-183)

### Page 181

```text
INTER-UNIVERSAL TEICHM¨ULLER THEORY III 181
The various indeterminacies (Ind1), (Ind2), (Ind3) to which the multiradial repre-
sentation is subject may be thought of as data that describes some sort of“formal
quotient”, like the “ﬁne moduli spaces” that appear in algebraic geometry.
In this context, theprocession-normalized mono-analytic log-volumes[i.e.,
where the average is taken overj∈ F⋇
l ] of Theorem 3.11, (i), (a), (c), furnish a
means of constructing a sort of associated“coarse space”or “inductive limit”
[of the “inductive system” constituted by this “formal quotient”] — i.e., in the
sense that [one veriﬁes immediately — cf. Proposition 3.9, (ii) — that] the re-
sulting log-volumes∈ R are invariantwith respect to the indeterminacies (Ind1),
(Ind2), and have the eﬀect of converting the indeterminacy (Ind3) into an in-
equality [from above]. Moreover, thelog-link compatibility of the various log-
volumes that appear [cf. Proposition 3.9, (iv); the ﬁnal portion of Theorem 3.11,
(ii)] ensures that these log-volumes arecompatiblewith [the portion of the “formal
quotient”/“inductive system” constituted by] the various arrows [i.e.,Kummer iso-
morphisms and log-links]o ft h elog-Kummer correspondenceof Theorem 3.11,
(ii). Here, we note that theaverages overj∈ F⋇
l that appear in the deﬁnition of
the procession-normalized volumes involved may be thought of as a consequence
of theF⋇
l -symmetry acting on the labels of the theta values that give rise to the
LGP-monoids — cf. also the deﬁnition of the symbol “∆” in [IUTchII], Corollary
4.10, (i), via the identiﬁcation of the symbols“0” and “⟨F⋇
l ⟩”; the discussion of
Remark 3.9.3. Also, in this context, it is of interest to observe that the various
tensor products that appear in the various local mono-analytic tensor packets
that arise in the multiradial representation of Theorem 3.11, (i), (a), have the ef-
fect ofidentifyingthe operation of “multiplication by elements ofZ” — and hence
also the eﬀect onlog-volumes of such multiplication operations! — atdiﬀerent
labels∈ F⋇
l .
(xi) For ease of reference, we divide thisstep into substeps, as follows.
(xi-a) Consider aq-pilot objectat (1,0), which we think of — relative to the
relevant copy of “F⊛
mod”—i nt e r m so ft h eholomorphic log-shells constructed
at (1,0) [cf. the discussion of Remark 3.12.2, (iv), (v), below]. Then the Θ×μ
LGP-
link from (0,0) to (1,0) may be interpreted as a sort ofgluing isomorphism
that relates the arithmetic holomorphic structure — i.e., the “conventional
ring/scheme-theory” —a t( 1,0) to the arithmetic holomorphic structure at (0,0)
in such a way that the Θ-pilot object at (0,0) [thought of as an object of the
relevant global realiﬁed Frobenioid] corresponds to theq-pilot objectat (1,0) [cf.
(i); the discussion of Remark 3.12.2, (ii), below].
(xi-b) On the other hand, the multiradial construction algorithm of Theorem
3.11, which was summarized in the discussion of (x), yields a construction of a
collection of possibilities of output datacontained in
(0,◦UQ⊇) 0,◦U
∼
→ 1,◦U (⊆ 1,◦UQ)
— where the isomorphism “
∼
→ ” arises from thepermutation symmetries dis-
cussed in the ﬁnal portion of Theorem 3.11, (i) — that satisﬁes theinput prime-
strip link (IPL)and simultaneous holomorphic expressibility (SHE)prop-
erties discussed in Remark 3.11.1, (iii), (iv), (v) [cf. also the discussion of“possible
```

### Page 182

```text
182 SHINICHI MOCHIZUKI
images” at the beginning of the present proof]. Here, with regard to (IPL), we ob-
serve that theF⊩▶-prime-strip portion of thelink/relationship of this collection
of possibilities of output data to theinput data (F⊩▶×μ-)prime-strip [cf. Re-
mark 3.11.1, (ii)] consists precisely of(full poly-)isomorphisms ofF⊩▶-prime-
strips, while the corresponding link/relationship forF⊣×μ-prime-strips is some-
what more complicated, as a result of theindeterminacies (Ind1), (Ind2), (Ind3).
Also, in this context, we observe that, although the multiradial construction algo-
rithm of Theorem 3.11 in fact involves the Θ-pilot object at (0,0), in the present
discussion of Step (xi), we shallonly be concernedwith qualitative logical as-
pects/consequences of this construction algorithm, i.e., with the
· input prime-strip link (IPL),
· simultaneous holomorphic expressibility (SHE),a n d
· algorithmic parallel transport (APT)
properties discussed in Remark 3.11.1, (iii), (iv), (v). That is to say, we shall
take the point of view of “temporarily forgetting” — cf. the discussion of
hidden internal structures (HIS)in Remark 3.11.1, (iv) — the fact that the
multiradial construction algorithm of Theorem 3.11 in fact involves Θ-pilot objects,
theta functions/values, mono-theta environments. Alternatively, in the discussion
tofollow, weshall, roughlyspeaking, thinkofthemultiradialconstructionalgorithm
of Theorem 3.11 as
“some” algorithm that transforms a certain type ofinput data into a
certain type ofoutput dataand, moreover, satisﬁescertain properties
(IPL) and (SHE).
(xi-c) Thus, the discussion of the (IPL) and (SHE) properties in (xi-b) may be
summarized as follows:
The multiradial construction algorithm of Theorem3.11 yields a collection
of possibilities of output data in1,◦U (⊆ 1,◦UQ)t h a ta r elinked/related
[cf. (IPL)], viaisomorphisms ofF⊩▶-prime-strips, to the representa-
tion [via thelog-Kummer correspondence in the 1-column] of theq-pilot
object at (1,0) on1,◦UQ, and, moreover, whose construction may be ex-
pressed entirely relative to thearithmetic holomorphic structure in
the 1-column [cf. (SHE)].
Here, we recall that, in more concrete language, this “arithmetic holomorphic struc-
ture in the 1-column” amounts, in essence, to thering structure labeled “1,◦”.
Moreover, by slightly enlarging the collection of possibilities of output data under
consideration by working with theholomorphic hull 1,◦U (⊇ 1,◦U), we obtain
output data that is expressed —not i nt e r m so fr e g i o n sc o n t a i n e di nv a r i o u stensor
products of local ﬁeldslabeled “1,◦” [i.e., more concretely, various isomorphs of
“Kv”, forv∈ V], but rather — in terms oflocalizations of arithmetic vector
bundles over certain local ringslabeled “1,◦” [i.e., more concretely, various iso-
morphs of “OKv”, forv∈ V] — cf. the discussion of Remarks 3.9.5, (vii), (Ob1),
(Ob2), (Ob5); 3.12.2, (v), below. Such an expression in terms of“localizations of
arithmetic vector bundles”is necessary in order to render the output data in a form
that iscomparable to the representation of theq-pilot object [i.e., which arises
from a certainarithmetic line bundle]a t( 1,0) on1,◦UQ.
```

### Page 183

```text
INTER-UNIVERSAL TEICHM¨ULLER THEORY III 183
(xi-d) The discussion of (xi-c) thus yields the following conclusion:
The multiradial construction algorithmof Theorem 3.11, followed by for-
mation of theholomorphic hull, yields a collection of possibilities of out-
put data in1,◦U that arelinked/related [cf. (IPL)], viaisomorphisms
of F⊩▶-prime-strips, to the representation [via the log-Kummer cor-
respondence in the 1-column]o ft h eq-pilot object at (1,0) on 1,◦UQ,
and, moreover, whose construction may be expressed entirely relative to
localizations of arithmetic vector bundlesover rings that arise in
the arithmetic holomorphic structurein the 1-column [cf. (SHE)].
Here, we observe that these “localizations of arithmetic vector bundles” are [unlike
thearithmetic line bundlethatgivesrisetothe q-pilot object]of rank> 1. Moreover,
the q-pilot object is deﬁned at the level ofrealiﬁcationsof Frobenioids of [global]
arithmetic line bundles. Thus, it is only by forming [a suitable positive tensor power
of] the determinant of the localizations of arithmetic vector bundles mentioned in
the above display [cf. Remark 3.9.5, (vii), (Ob3), (Ob4)] and then applying the
[suitably normalized, with respect toj∈| Fl|] log-volume to various regions —
i.e., theregion1,◦U and theregionthat arises from the representation of theq-pilot
object at (1,0) on1,◦UQ —i n1,◦UQ [cf. Remark 3.9.5, (vii), (Ob3), (Ob4), (Ob6),
(Ob7), (Ob9)], that we are able to obtaincompletely comparable objects [cf.
Remarks 3.9.5, (vii), (Ob5), (Ob6), (Ob7), (Ob8), (Ob9); 3.9.5, (viii), (ix)], namely,
R≤−|log(Θ)|
def
={λ∈ R| λ≤−| log(Θ)|} ⊆R; −| log(q)|∈ R
—wherewerecallthat, bydeﬁnition, −|log(Θ)|isthe[ negative—cf. thediscussion
of “possible images”at the beginning of the present proof] log-volume of1,◦U, while
−| log(q)| is the log-volume of the region that arises from the representation of
the q-pilot object at (1,0) on 1,◦UQ. In this context, it is useful to recall from
Proposition 3.9, (iii) [cf. also the discussion of Remarks 3.9.2, 3.9.6], thatglobal
arithmetic degrees of objects of global realiﬁed Frobenioids may be interpreted
as log-volumes [cf. also the discussion of Remarks 1.5.2, (iii); 3.10.1, (iv), as
well as of Remark 3.12.2, (v), below]. Finally, in this context, we observe [cf.
the ﬁrst display of the present (xi-d)] that it is ofcrucial importance to apply
the log-Kummer correspondence in the 1-column [cf. the discussion of log-
Kummer correspondencesin Remark 3.9.5, (vii), (Ob7), (Ob8); Remark 3.9.5, (viii),
(sQ4); Remark 3.9.5, (ix); the ﬁnal portion of Remark 3.9.5, (x); the discussion
of the ﬁnal portion of Remark 3.12.2, (v), below], in order torectify thevertical
shift/mismatch[cf. thediscussionof(iii), (iv)inthecaseofthe0 -column]between
the unit portion of 1,0F⊩▶×μ
∆ and thelog-shells arising from [the image via the
relevant Kummer isomorphisms of] this unit portion, which give rise to thetensor
packets of log-shellsthat constitute1,◦U.
(xi-e) Next, let us recall that the relationship, i.e., that arises by applying the
log-volume to the pilot-object, between the pilot-object log-volume −| log(q)|
∈ R and theinput data (F⊩▶×μ-)prime-strip is precisely the relationshippre-
scribed/imposed by thearithmetic holomorphic structurein the 1-column,
i.e., via the representation of the input data (F⊩▶×μ-)prime-strip on1,◦U relative
```

## IUT IV - Theorem 1.10 normalization (pp. 22-23)

### Page 22

```text
22 SHINICHI MOCHIZUKI
as thenormalized degreeof a. Thus, for any ﬁnite extensionK of F,w eh a v e
deg(a|K)=d e g(a)
—w h e r ew ew r i t ed e g(a|K) for the normalized degree of the pull-back a|K ∈
ADivR(K) [deﬁned in the evident fashion] ofa to K.
(ii) Let vQ ∈ VQ
def
= V(Q), E ⊆ V(F) a nonempty set of elements lying over
vQ.I f a =
∑
v∈V(F)
cv ·v ∈ ADivR(F), then we shall write
aE
def
=
∑
v∈E
cv ·v ∈ ADivR(F); deg E(a)
def
= deg(aE)∑
v∈E
[Fv : QvQ]
for the portion ofa supported inE and the“normalizedE-degree”of a, respectively.
Thus, for any ﬁnite extensionK of F,w eh a v e
degE|K (a|K)=d e gE(a)
—w h e r ew ew r i t eE|K ⊆ V(K) for the set of valuations lying over valuations∈ E.
Theorem 1.10. (Log-volume Estimates for Θ-Pilot Objects) Fix a col-
lection of initial Θ-data as in [IUTchI], Deﬁnition 3.1. Suppose that we are
in the situation of [IUTchIII], Corollary 3.12, and that the elliptic curveEF has
good reduction at every valuation∈ V(F)good ⋂ V(F)non that doesnot divide
2l. In the notation of [IUTchI], Deﬁnition 3.1, let us writedmod
def
=[ Fmod : Q],
(1 ≤) emod (≤ dmod) for themaximal ramiﬁcation indexof Fmod [i.e., of valu-
ations ∈ Vnon
mod] over Q, d∗
mod
def
=2 12 ·33 ·5·dmod, e∗
mod
def
=2 12 ·33 ·5·emod (≤ d∗
mod),
and
Fmod ⊆ Ftpd
def
= Fmod( EFmod[2] ) ⊆ F
for the“tripodal” intermediate ﬁeld obtained fromFmod by adjoining the ﬁelds of
deﬁnition of the2-torsion points of any model ofEF×FF over Fmod [cf. Proposition
1.8, (ii), (iii)]. Moreover, we assume that the(3·5)-torsion points ofEF are deﬁned
over F, and that
F = Fmod(
√
−1,E Fmod[2·3·5] )
def
= Ftpd(
√
−1,E Ftpd[3·5] )
— i.e., thatF is obtained fromFtpd by adjoining √−1, together with the ﬁelds of
deﬁnition of the(3·5)-torsion points of a modelEFtpd of the elliptic curveEF ×F F
over Ftpd determined by theLegendre formof the Weierstrass equation [cf., e.g.,
the statement of Corollary 2.2, below; Proposition 1.8, (vi)]. [Thus, it follows
from Proposition 1.8, (iv), thatEF ∼= EFtpd ×Ftpd F over F, and from [IUTchI],
Deﬁnition 3.1, (c), thatl ⁄=5 .] If Fmod ⊆ F□ ⊆ K is any intermediate extension
which is Galois overFmod, then we shall write
dF□
ADiv ∈ ADivR(F□)
```

### Page 23

```text
INTER-UNIVERSAL TEICHM¨ULLER THEORY IV 23
for the eﬀective arithmetic divisor determined by thediﬀerent ideal of F□ over
Q,
qF□
ADiv ∈ ADivR(F□)
for the eﬀective arithmetic divisor determined by theq-parameters of the elliptic
curve EF at the elements ofV(F□)bad def
= Vbad
mod ×Vmod V(F□)( ⁄= ∅) [cf. [GenEll],
Remark 3.3.1],
fF□
ADiv ∈ ADivR(F□)
for the eﬀective arithmetic divisor whose support coincides withSupp(qF□
ADiv),b u t
all of whose coeﬃcients are equal to1 — i.e., theconductor —a n d
log(dF□
v )
def
=d e gV(F□)v(dF□
ADiv) ∈ R≥0; log( dF□
vQ )
def
=d e gV(F□)vQ
(dF□
ADiv) ∈ R≥0
log(dF□)
def
=d e g(dF□
ADiv) ∈ R≥0
log(qv)
def
=d e gV(F□)v(qF□
ADiv) ∈ R≥0; log( qvQ)
def
=d e gV(F□)vQ
(qF□
ADiv) ∈ R≥0
log(q)
def
=d e g(qF□
ADiv) ∈ R≥0
log(fF□
v )
def
=d e gV(F□)v(fF□
ADiv) ∈ R≥0; log( fF□
vQ )
def
=d e gV(F□)vQ
(fF□
ADiv) ∈ R≥0
log(fF□)
def
=d e g(fF□
ADiv) ∈ R≥0
—w h e r ev ∈ Vmod = V(Fmod), vQ ∈ VQ = V(Q), V(F□)v
def
= V(F□) ×Vmod {v},
V(F□)vQ
def
= V(F□) ×VQ {vQ}. Here, we observe that the various “log(q(−))’s” are
independent of the choice ofF□, and that the quantity “|log(q)|∈ R>0” deﬁned in
[IUTchIII], Corollary 3.12, is equal to 1
2l · log(q) ∈ R [cf. the deﬁnition of “q
v
”
in [IUTchI], Example 3.2, (iv)]. Then one may take the constant “CΘ ∈ R”o f
[IUTchIII], Corollary 3.12, to be
l+1
4·|log(q)| ·
{
(1+ 12·dmod
l )·(log(dFtpd)+log( fFtpd))+10 ·(e∗
mod ·l+ηprm)
− 1
6 ·(1− 12
l2 )·log(q)
}
−1
and hence, by applying the inequality “CΘ ≥− 1” of [IUTchIII], Corollary 3.12,
conclude that
1
6 ·log(q) ≤ (1+ 20·dmod
l )·(log(dFtpd)+log( fFtpd))+20 ·(e∗
mod ·l+ηprm)
≤ (1+ 20·dmod
l )·(log(dF)+log( fF))+20 ·(e∗
mod ·l+ηprm)
—w h e r eηprm is the positive real number of Proposition 1.6.
Proof. For ease of reference, we divide our discussion intosteps, as follows.
(i) We begin by recalling the followingelementary identitiesfor n ∈ N≥1:
(E1) 1
n
n∑
m=1
m = 1
2(n+1);
(E2) 1
n
n∑
m=1
m2 = 1
6(2n+1)(n+1).
```

## IUT IV - Theorem 1.10 proof, Steps (iv)-(v) (pp. 27-29)

### Page 27

```text
INTER-UNIVERSAL TEICHM¨ULLER THEORY IV 27
Thus, we proceed to estimate this log-volume ateach vQ ∈ VQ. Once one ﬁxesvQ,
this amounts to estimating the component of this log-volume in
“IQ(S±
j+1;n,◦D⊣
vQ)”
[cf. the notation of [IUTchIII], Theorem 3.11, (i), (a)], foreach j ∈{ 1,...,l ⋇},
which we shall also regard as an element ofF⋇
l , and then computing theaverage,
over j ∈{ 1,...,l ⋇}, of these estimates. Here, we recall [cf. [IUTchI], Proposition
6.9, (i); [IUTchIII], Proposition 3.4, (ii)] thatS±
j+1 = {0,1,...,j }. Also, we recall
from [IUTchIII], Proposition 3.2, that “IQ(S±
j+1;n,◦D⊣
vQ)” is, by deﬁnition, atensor
productof j+1 copies, indexed by the elements ofS±
j+1,o ft h edirect sumof theQ-
spansofthe log-shellsassociatedtoeachoftheelementsof V(Fmod)vQ [cf., especially,
the second and third displays of [IUTchIII], Proposition 3.2]. In particular, foreach
collection
{vi}i∈S±
j+1
of [not necessarily distinct!] elements of V(Fmod)vQ, we must estimate the com-
ponent of the log-volume in question corresponding to thetensor product of the
Q-spans of thelog-shells associated to this collection{vi}i∈S±
j+1
and then compute
the weighted average[cf. the discussion of Remark 1.7.1], over possible collections
{vi}i∈S±
j+1
, of these estimates.
(v) LetvQ ∈ Vdst
Q . Fix j, {vi}i∈S±
j+1
as in Step (iv). Writevi ∈ V
∼
→ Vmod =
V(Fmod) for the element corresponding tovi. We would like to apply Proposition
1.4, (iii), to the present situation, by taking
· “I”t ob eS±
j+1;
· “I∗ ⊆ I” to be the set ofi ∈ I such thatevi
>p vQ −2;
· “ki”t ob eKvi
[so “Ri” will be the ring of integersOKvi
of Kvi
];
· “i†”t ob ej ∈ S±
j+1;
· “λ”t ob e0i fvj ∈ Vgood;
· “λ” to be “ord(−)” of the element qj2
vj
[cf. the deﬁnition of “q
v
”i n
[IUTchI], Example 3.2, (iv)] ifvj ∈ Vbad.
Thus, theinclusion “φ(pλ · (RI)∼) ⊆ p⌊λ−dI−aI⌋· logp(R×
I )” of Proposition 1.4,
(iii), implies that the result of multiplying “p⌊λ⌋−|I| ·2−|I| ·logp(R×
I )” by a suitable
nonpositive[cf. theinequalitiesconcerning“ dI+aI”thatconstitutetheﬁnalportion
of Proposition 1.4, (iii)] integer power ofpvQ containsthe “union of possible images
ofaΘ-pilotobject”discussedinStep(iv). Thatistosay, the indeterminacies(Ind1)
and (Ind2) are taken into account by thearbitrarynature of the automorphism “φ”
[cf. Proposition 1.2], while theindeterminacy (Ind3) is taken into account by the
fact that we are consideringupper bounds[cf. the discussion of Step (x) of the proof
of [IUTchIII], Corollary 3.12], together with the fact that the above-mentioned
integer power of pvQ is nonpositive, which implies that the module obtained by
multiplying by this power ofpvQ contains “p⌊λ⌋−|I| · 2−|I| · logp(R×
I )”. Thus, an
upper bound on the component of the log-volume of theholomorphic hull under
```

### Page 28

```text
28 SHINICHI MOCHIZUKI
consideration may be obtained by computing an upper bound for the log-volume of
the right-hand side of the inclusion “p⌊λ−dI−aI⌋·logp(R×
I ) ⊆ p⌊λ−dI−aI⌋−bI ·(RI)∼”
of Proposition 1.4, (iii). Such anupper bound
“
(
−λ+ dI +1
)
·log(p)+
∑
i∈I∗
{3+log( ei)}”
is given in the second displayed inequality of Proposition 1.4, (iii). Here, we note
that ifevi ≤ pvQ −2 for alli ∈ I, then thisupper boundassumes the form
“
(
−λ+ dI +1
)
·log(p)”.
On the other hand, by (R4), ifevi
>p vQ − 2f o rs o m ei ∈ I, then it follows that
pvQ ≤ e∗
mod ·l, and log(evi) ≤− 3+4 ·log(e∗
mod ·l), so theupper boundin question
may be taken to be
“
(
−λ+ dI +1
)
·log(p)+4 ( j +1) ·l∗
mod”
—w h e r ew ew r i t el∗
mod
def
= log(e∗
mod ·l). Also, we note that, unlike the other terms
that appear in theseupper bounds,“ λ”i s asymmetric with respect to the choice
of “i† ∈ I”i n S±
j+1. Since we would like to computeweighted averages [cf. the
discussion of Remark 1.7.1], we thus observe that, aftersymmetrizing with respect
to the choice of “i† ∈ I”i n S±
j+1,t h i supper boundmay be written in the form
“β⃗e”
[cf. the notation of Proposition 1.7] if, in the situation of Proposition 1.7, one takes
· “E”t ob eV(Fmod)vQ;
· “n”t ob e j +1 ,s oa ne l e m e n t“⃗e ∈ En” corresponds precisely to a
collection {vi}i∈S±
j+1
;
· “λe”, for an elemente ∈ E corresponding tov ∈ V(Fmod)= Vmod,t ob e
[(Fmod)v : QvQ] ∈ R>0;
· “βe”, for an elemente ∈ E corresponding tov ∈ V(Fmod)= Vmod,t ob e
log(dK
v )− j2
2l(j+1) ·log(qv)+ 1
j+1 ·log(pvQ)+4 ·ιvQ ·l∗
mod
— where we recall thatιvQ
def
=1i f pvQ ≤ e∗
mod ·l, ιvQ
def
=0i f pvQ >e ∗
mod ·l.
Here, we note that it follows immediately from the ﬁrst equality of the ﬁrst dis-
play of Proposition 1.7 that, after passing toweighted averages, the operation of
symmetrizing with respect to the choice of “i† ∈ I”i nS±
j+1 does not aﬀectthe com-
putation of theupper boundunder consideration. Thus, by applying Proposition
1.7, we obtain that the resulting“weighted average upper bound”is given by
(j +1) ·log(dK
vQ)− j2
2l ·log(qvQ)+log( sQ
vQ)+4( j +1) ·l∗
mod ·log(s≤
vQ)
```

### Page 29

```text
INTER-UNIVERSAL TEICHM¨ULLER THEORY IV 29
— where we recall the notational conventions introduced in Step (iii). Thus, it
remains to compute theaverage overj ∈ F⋇
l .B y averaging over j ∈{ 1,...,l ⋇ =
l−1
2 } and applying (E1), (E2), we obtain the“procession-normalized upper
bound”
(l⋇+3)
2 ·log(dK
vQ)− (2l⋇+1)(l⋇+1)
12l ·log(qvQ)+log( sQ
vQ)+2( l⋇ +3) ·l∗
mod ·log(s≤
vQ)
= l+5
4 ·log(dK
vQ)− l+1
24 ·log(qvQ)+log( sQ
vQ)+( l+5) ·l∗
mod ·log(s≤
vQ)
≤ l+1
4 ·
{
(1+ 4
l )·log(dK
vQ)− 1
6 ·log(qvQ)+ 4
l ·log(sQ
vQ)+ 20
3 ·l∗
mod ·log(s≤
vQ)
}
— where, in the passage to the ﬁnal displayed inequality, we apply the estimates
1
l+1 ≤ 1
l and 4(l+5)
l+1 ≤ 20
3 , both of which may be regarded as consequences of the
fact thatl ≥ 5.
(vi) Next, let vQ ∈ Vnon
Q \ Vdst
Q . Fix j, {vi}i∈S±
j+1
as in Step (iv). Write
vi ∈ V
∼
→ Vmod = V(Fmod) for the element corresponding tovi. We would like to
apply Proposition 1.4, (iv), to the present situation, by taking
· “I”t ob eS±
j+1;
· “ki”t ob eKvi
[so “Ri” will be the ring of integersOKvi
of Kvi
].
Here, we note that our assumption thatvQ ∈ Vnon
Q \Vdst
Q implies that the hypotheses
of Proposition 1.4, (iv), are satisﬁed. Thus, theinclusion “φ((RI)∼) ⊆ (RI)∼”o f
Proposition 1.4, (iv), implies that the tensor product of log-shells under consider-
ation contains the “union of possible images of a Θ-pilot object” discussed in Step
(iv). That is to say, theindeterminacies (Ind1) and (Ind2) are taken into account
by the arbitrary nature of the automorphism “φ” [cf. Proposition 1.2], while the
indeterminacy (Ind3) is taken into account by the fact that we are consideringupper
bounds [cf. the discussion of Step (x) of the proof of [IUTchIII], Corollary 3.12],
together with the fact that the “container of possible images” isprecisely equalto
the tensor product of log-shells under consideration. Thus, an upper bound on the
component of the log-volume under consideration may be obtained by computing
an upper bound for the log-volume of the right-hand side “(RI)∼” of the above
inclusion. Such anupper bound
“0”
is given in the ﬁnal equality of Proposition 1.4, (iv). One may then compute a
“weighted average upper bound” a n dt h e na“procession-normalized upper
bound”, as was done in Step (v). The resulting“procession-normalized upper
bound” is clearly equal to 0.
(vii) Next, let vQ ∈ Varc
Q . Fix j, {vi}i∈S±
j+1
as in Step (iv). Write vi ∈
V
∼
→ Vmod = V(Fmod) for the element corresponding to vi. We would like to
apply Proposition 1.5, (iii), (iv), to the present situation, by taking
· “I”t ob eS±
j+1 [so |I| = j +1];
· “V”t ob eV(Fmod)vQ;
```

---

## Curated display index (for abc/qpilot transcription)

### IUT III, Cor 3.12 (pp. 173-174)

```text
−| log(Θ)| ∈ R ⋃ {+∞}
−| log(q)| ∈ R
−| log(Θ)| ≥ −| log(q)|
C_Θ ≥ −1  for any C_Θ ∈ R with −| log(Θ)| ≤ C_Θ·|log(q)|
```

Location: statement begins p. 173 line 10326 of `III.txt`; inequality p. 173-174.

### IUT III, Cor 3.12 proof, Step (xi-d) (p. 183)

```text
R_{≤−|log(Θ)|} := {λ ∈ R | λ ≤ −|log(Θ)|} ⊆ R;   −|log(q)| ∈ R
−|log(Θ)| is the [negative] log-volume of 1,◦U
−|log(q)| is the log-volume of the region arising from the q-pilot representation at (1,0) on 1,◦UQ
```

Location: p. 183, lines 10844-10851 of `III.txt`.

### IUT III, Theorem 3.11 Ind3 (p. 156)

```text
(Ind3) as one varies m ∈ Z, the isomorphisms of (a) are “upper semi-compatible”, relative to the log-links of the n-th column of the LGP-Gaussian log-theta-lattice under consideration, in a sense that involves certain natural inclusions “⊆” at vQ∈V_non_Q and certain natural surjections “↠” at vQ∈V_arc_Q — cf. Proposition 3.5, (ii), (a), (b), for more details.
Finally, as one varies m ∈ Z, the isomorphisms of (a) are [precisely!] compatible, relative to the log-links of the n-th column ... with the respective log-volumes [cf. Proposition 3.9, (iv)].
```

Location: p. 156, lines 9441-9451 of `III.txt`.

### IUT III, Step (x) conversion of Ind3 to an upper-bound inequality (p. 181)

```text
the procession-normalized mono-analytic log-volumes [i.e., where the average is taken over j∈F⋇_l] of Theorem 3.11, (i), (a), (c), furnish a means of constructing a sort of associated “coarse space” ... [one verifies immediately — cf. Proposition 3.9, (ii) — that] the resulting log-volumes ∈ R are invariant with respect to the indeterminacies (Ind1), (Ind2), and have the effect of converting the indeterminacy (Ind3) into an inequality [from above].
```

Location: p. 181, lines 10724-10732 of `III.txt`.

### IUT IV, normalization (p. 23)

```text
|log(q)| ∈ R_{>0} ... is equal to  1/(2l)·log(q) ∈ R   [cf. the definition of “q_v” in [IUTchI], Example 3.2, (iv)].
```

Location: p. 23, lines 1359-1365 of `IV.txt`.

### IUT IV, Step (v) displays (pp. 27-29)

1. Tensor/log-shell reduction (p. 27):
```text
IQ(S±_{j+1}; n,◦D⊣_{vQ}) is a tensor product of j+1 copies, indexed by S±_{j+1} = {0,1,...,j},
of the direct sum of the Q-spans of the log-shells at the elements of V(F_mod)_{vQ}.
For each collection {v_i}_{i∈S±_{j+1}}, estimate the tensor-product component and
compute the weighted average over possible collections.
```
2. The q-term before averaging (p. 28):
```text
(j+1)·log(d^K_{vQ}) − j²/(2l)·log(q_{vQ}) + log(s^Q_{vQ}) + 4(j+1)·l*_mod·log(s^≤_{vQ})
```
3. Procession-normalized upper bound after averaging over j ∈ {1,...,l⋇=(l−1)/2} (p. 29):
```text
(l⋇+3)/2·log(d^K_{vQ}) − (2l⋇+1)(l⋇+1)/(12l)·log(q_{vQ}) + log(s^Q_{vQ})
  + 2(l⋇+3)·l*_mod·log(s^≤_{vQ})
= (l+5)/4·log(d^K_{vQ}) − (l+1)/24·log(q_{vQ}) + log(s^Q_{vQ})
  + (l+5)·l*_mod·log(s^≤_{vQ})
≤ (l+1)/4 · { (1 + 4/l)·log(d^K_{vQ}) − 1/6·log(q_{vQ}) + 4/l·log(s^Q_{vQ})
  + 20/3·l*_mod·log(s^≤_{vQ}) }
```
4. Final Theorem 1.10 conclusion (p. 23):
```text
1/6·log(q) ≤ (1 + 20·d_mod/l)·(log(d_Ftpd)+log(f_Ftpd)) + 20·(e*_mod·l+η_prm)
≤ (1 + 20·d_mod/l)·(log(d_F)+log(f_F)) + 20·(e*_mod·l+η_prm)
```

Notes:
- The `− j²/(2l)·log(q_{vQ})` coefficient is the origin of the `j²/(2ℓ)` q-term.
- The `j`-average gives `−(l+1)/24·log(q_{vQ})`; in `l=5` this is `−6/24 = −1/4`.
- The final `1/6·log(q)` bound comes from the `−1/6(1−12/l²)log(q)` term in `C_Θ`.
