# IUT-TEXT-N5 - contiguous OCR excerpts for N5 (A1041)

Source: `coord/IUT-TEXT/III.txt`, `IV.txt` (pypdf extraction of the IUT PDFs).
Each line is prefixed with its global source line number so displays can be cited
as `III:NNNN` / `IV:NNNN`; OCR line breaks and artifacts are preserved.

## Display index (source line numbers)

IUT III:
- `n,◦U` / `n,◦UQ` hull/union definitions: III:10361-10404.
- proof assumption `−|log Θ|<0` and compactness: III:10356-10414.
- Step (x) indeterminacies summary: III:10701-10751.
- Step (x) log-volumes convert Ind3 to upper inequality: III:10724-10732.
- Step (xi-a) q-pilot/Θ-pilot gluing: III:10752-10763.
- Step (xi-b) IPL/SHE output data: III:10764-10800.
- Step (xi-c) hull enlargement and arithmetic vector bundles: III:10801-10822.
- Step (xi-d) determinant/log-volume and `R_{<=-|log Θ|}`, `-|log(q)|`: III:10825-10870.

IUT IV:
- Step (iv) instruction to bound hull log-volume: IV:1585-1625.
- Step (v) tensor/log-shell reduction: IV:1626-1650.
- Step (v) inclusion/upper-bound displays: IV:1651-1686.
- Step (v) symmetrization and weighted average: IV:1706-1743.
- Step (v) q-term and procession-normalized bound: IV:1737-1785.

## IUT III pp. 174-175: Cor 3.12 proof beginning, hull/union definitions

### Page 174

```text
[10337] 174 SHINICHI MOCHIZUKI
[10338] relative to the relevantKummer isomorphisms [cf. Theorem 3.11, (ii)], in the
[10339] multiradial representationof Theorem 3.11, (i), which we regard assubject to
[10340] the indeterminacies (Ind1), (Ind2), (Ind3) described in Theorem 3.11, (i), (ii).
[10341] Write
[10342] −| log(q)|∈ R
[10343] for the procession-normalized mono-analytic log-volume of the image of a
[10344] q-pilot object[cf. Deﬁnition 3.8, (i)], relative to the relevantKummer isomor-
[10345] phisms [cf. Theorem 3.11, (ii)], in themultiradial representationof Theorem
[10346] 3.11, (i), which we donot regard as subject to the indeterminacies(Ind1), (Ind2),
[10347] (Ind3) described in Theorem 3.11, (i), (ii). Here, we recall the deﬁnition of the
[10348] symbol “∆” as the result of identifying thelabels
[10349] “0”a n d“⟨F⋇
[10350] l ⟩”
[10351] [cf. [IUTchII], Corollary 4.10, (i)]. In particular,|log(q)| > 0 is easily computed
[10352] in terms of the various q-parameters of the elliptic curve EF [cf. [IUTchI],
[10353] Deﬁnition 3.1, (b)] atv∈ Vbad (⁄=∅). Then it holds that−| log(Θ)|∈ R,a n d
[10354] −| log(Θ)|≥−| log(q)|
[10355] — i.e.,CΘ≥− 1 for any real numberCΘ∈ R such that−| log(Θ)|≤ CΘ·|log(q)|.
[10356] Proof. We begin by observing that, since|log(q)| > 0, we mayassume without loss
[10357] of generalityin the remainder of the proof that
[10358] −| log(Θ)| < 0
[10359] whenever−| log(Θ)|∈ R [i.e., since an inequality−| log(Θ)|≥ 0 would imply
[10360] that−| log(Θ)|≥ 0 > −|log(q)|]. Now suppose that we are in the situation of
[10361] Theorem 3.11. Forn∈ Z,w r i t e
[10362] n,◦U
[10363] def
[10364] =
[10365] {
[10366] n,◦Uj,vQ
[10367] }
[10368] j∈|Fl|,vQ∈VQ
[10369] ⊆ n,◦UQ def
[10370] =
[10371] {
[10372] n,◦UQ
[10373] j,vQ
[10374] }
[10375] j∈|Fl|,vQ∈VQ
[10376] [where we observe that the “⊆” constitutes a slight abuse of notation] for the
[10377] collection of subsetsn,◦Uj,vQ ⊆ n,◦UQ
[10378] j,vQ
[10379] def
[10380] = IQ(S±
[10381] j+1;n,◦D⊣
[10382] vQ) [cf. Theorem 3.11, (i),
[10383] (a)] given by the variousunions,f o rj∈| Fl| and vQ∈ VQ,o ft h epossible images
[10384] of a Θ-pilot object [cf. Deﬁnition 3.8, (i)], relative to the relevant Kummer
[10385] isomorphisms [cf. Theorem 3.11, (ii)], in the multiradial representation of
[10386] Theorem 3.11, (i), which we regard assubject to the indeterminacies (Ind1),
[10387] (Ind2), (Ind3) described in Theorem 3.11, (i), (ii);
[10388] n,◦U =
[10389] {
[10390] n,◦Uj,vQ
[10391] }
[10392] j∈|Fl|,vQ∈VQ
[10393] ⊆ n,◦UQ =
[10394] {
[10395] n,◦UQ
[10396] j,vQ
[10397] }
[10398] j∈|Fl|,vQ∈VQ
[10399] [where we observe that the “⊆” constitutes a slight abuse of notation] for the col-
[10400] lection of subsetsn,◦Uj,vQ ⊆ n,◦UQ
[10401] j,vQ =IQ(S±
[10402] j+1;n,◦D⊣
[10403] vQ) [cf. Theorem 3.11, (i), (a)]
[10404] given by the variousholomorphic hulls [cf. Remark 3.9.5, (i)] of the subsets
```

### Page 175

```text
[10406] INTER-UNIVERSAL TEICHM¨ULLER THEORY III 175
[10407] n,◦Uj,vQ ⊆I Q(S±
[10408] j+1;n,◦D⊣
[10409] vQ), relative to the arithmetic holomorphic structure labeled
[10410] “n,◦”. Here, we observe that one concludes easily from the [easily veriﬁed]com-
[10411] pactnessof the1,◦Uj,vQ [where j∈| Fl|, vQ∈ VQ], together with the deﬁnition of the
[10412] log-volume, that the quantity−| log(Θ)| is ﬁnite, hencenegative[by ourassumption
[10413] at the beginning of the present proof!]. In particular, we observe [cf. Remark 2.4.2,
[10414] (iv), (v), (vi); Remark 3.9.6; Remark 3.9.7; the discussion of “IPL” in Remark
[10415] 3.11.1, (iii)] that
[10416] we may restrict our attention topossible images of a Θ-pilot object
[10417] thatcorrespondtodata[i.e., collectionsofregions]thatmaybeinterpreted
[10418] as anF⊩▶-prime-strip.
[10419] Now we proceed to review precisely what is achieved by the various portions of
[10420] Theorem 3.11 and, indeed, by the theory developed thus far in the present series of
[10421] papers. This review leads naturally to an interpretation of the theory that gives rise
[10422] to theinequality asserted in the statement of Corollary 3.12. For ease of reference,
[10423] we divide our discussion intosteps, as follows.
[10424] (i) In the following discussion, we concentrate on asingle arrow— i.e., asingle
[10425] Θ×μ
[10426] LGP-link
[10427] 0,0HT Θ±ellNF Θ×μ
[10428] LGP
[10429] −→ 1,0HT Θ±ellNF
[10430] — of the [LGP-Gaussian] log-theta-lattice under consideration. This arrow consists
[10431] of thefull poly-isomorphismofF⊩▶×μ-prime-strips
[10432] 0,0F⊩▶×μ
[10433] LGP
[10434] ∼
[10435] → 1,0F⊩▶×μ
[10436] ∆
[10437] [cf. Deﬁnition 3.8, (ii)]. This poly-isomorphism may be thought of as consisting of
[10438] a “unit portion” constituted by the associated [full] poly-isomorphism ofF⊣×μ-
[10439] prime-strips
[10440] 0,0F⊣×μ
[10441] LGP
[10442] ∼
[10443] → 1,0F⊣×μ
[10444] ∆
[10445] anda “value group portion”constitutedbytheassociated[full]poly-isomorphism
[10446] ofF⊩▶-prime-strips
[10447] 0,0F⊩▶
[10448] LGP
[10449] ∼
[10450] → 1,0F⊩▶
[10451] ∆
[10452] [cf. Deﬁnition 2.4, (iii)]. This value group portion of the Θ×μ
[10453] LGP-link maps Θ-pilot
[10454] objects of 0,0HT Θ±ellNF to q-pilot objectsof 1,0HT Θ±ellNF [cf. Remark 3.8.1].
[10455] (ii) Whereas the units of the Frobenioids that appear in theF⊣×μ-prime-strip
[10456] 0,0F⊣×μ
[10457] LGP are subject to AutF⊣×μ(−)-indeterminacies [i.e., “(Ind1), (Ind2)” — cf.
[10458] Theorem 3.11, (iii), (a), (b)], thecyclotomes that appear in the Kummer theory
[10459] surrounding the ´etale theta function and κ-coric functions, i.e., which give
[10460] rise to the “value group portion”0,0F⊩▶
[10461] LGP,a r einsulated from these AutF⊣×μ(−)-
[10462] indeterminacies — cf. Theorem 3.11, (iii), (c), (d); the discussion of Remark
[10463] 3.11.3, (iv); Fig. 3.6 below. Here, we recall that in the case of the ´etale theta
[10464] function, this follows from the theory of§2, i.e., in essence, from thecyclotomic
[10465] rigidity of mono-theta environments, as discussed in [EtTh]. On the other
[10466] hand, in the case ofκ-coric functions, this follows from the algorithms discussed in
[10467] [IUTchI], Example 5.1, (v); [IUTchI], Deﬁnition 5.2, (vi), (viii).
```

## IUT III pp. 181-183: Cor 3.12 proof Step (x) and Step (xi-a/c/d)

### Page 181

```text
[10720] INTER-UNIVERSAL TEICHM¨ULLER THEORY III 181
[10721] The various indeterminacies (Ind1), (Ind2), (Ind3) to which the multiradial repre-
[10722] sentation is subject may be thought of as data that describes some sort of“formal
[10723] quotient”, like the “ﬁne moduli spaces” that appear in algebraic geometry.
[10724] In this context, theprocession-normalized mono-analytic log-volumes[i.e.,
[10725] where the average is taken overj∈ F⋇
[10726] l ] of Theorem 3.11, (i), (a), (c), furnish a
[10727] means of constructing a sort of associated“coarse space”or “inductive limit”
[10728] [of the “inductive system” constituted by this “formal quotient”] — i.e., in the
[10729] sense that [one veriﬁes immediately — cf. Proposition 3.9, (ii) — that] the re-
[10730] sulting log-volumes∈ R are invariantwith respect to the indeterminacies (Ind1),
[10731] (Ind2), and have the eﬀect of converting the indeterminacy (Ind3) into an in-
[10732] equality [from above]. Moreover, thelog-link compatibility of the various log-
[10733] volumes that appear [cf. Proposition 3.9, (iv); the ﬁnal portion of Theorem 3.11,
[10734] (ii)] ensures that these log-volumes arecompatiblewith [the portion of the “formal
[10735] quotient”/“inductive system” constituted by] the various arrows [i.e.,Kummer iso-
[10736] morphisms and log-links]o ft h elog-Kummer correspondenceof Theorem 3.11,
[10737] (ii). Here, we note that theaverages overj∈ F⋇
[10738] l that appear in the deﬁnition of
[10739] the procession-normalized volumes involved may be thought of as a consequence
[10740] of theF⋇
[10741] l -symmetry acting on the labels of the theta values that give rise to the
[10742] LGP-monoids — cf. also the deﬁnition of the symbol “∆” in [IUTchII], Corollary
[10743] 4.10, (i), via the identiﬁcation of the symbols“0” and “⟨F⋇
[10744] l ⟩”; the discussion of
[10745] Remark 3.9.3. Also, in this context, it is of interest to observe that the various
[10746] tensor products that appear in the various local mono-analytic tensor packets
[10747] that arise in the multiradial representation of Theorem 3.11, (i), (a), have the ef-
[10748] fect ofidentifyingthe operation of “multiplication by elements ofZ” — and hence
[10749] also the eﬀect onlog-volumes of such multiplication operations! — atdiﬀerent
[10750] labels∈ F⋇
[10751] l .
[10752] (xi) For ease of reference, we divide thisstep into substeps, as follows.
[10753] (xi-a) Consider aq-pilot objectat (1,0), which we think of — relative to the
[10754] relevant copy of “F⊛
[10755] mod”—i nt e r m so ft h eholomorphic log-shells constructed
[10756] at (1,0) [cf. the discussion of Remark 3.12.2, (iv), (v), below]. Then the Θ×μ
[10757] LGP-
[10758] link from (0,0) to (1,0) may be interpreted as a sort ofgluing isomorphism
[10759] that relates the arithmetic holomorphic structure — i.e., the “conventional
[10760] ring/scheme-theory” —a t( 1,0) to the arithmetic holomorphic structure at (0,0)
[10761] in such a way that the Θ-pilot object at (0,0) [thought of as an object of the
[10762] relevant global realiﬁed Frobenioid] corresponds to theq-pilot objectat (1,0) [cf.
[10763] (i); the discussion of Remark 3.12.2, (ii), below].
[10764] (xi-b) On the other hand, the multiradial construction algorithm of Theorem
[10765] 3.11, which was summarized in the discussion of (x), yields a construction of a
[10766] collection of possibilities of output datacontained in
[10767] (0,◦UQ⊇) 0,◦U
[10768] ∼
[10769] → 1,◦U (⊆ 1,◦UQ)
[10770] — where the isomorphism “
[10771] ∼
[10772] → ” arises from thepermutation symmetries dis-
[10773] cussed in the ﬁnal portion of Theorem 3.11, (i) — that satisﬁes theinput prime-
[10774] strip link (IPL)and simultaneous holomorphic expressibility (SHE)prop-
[10775] erties discussed in Remark 3.11.1, (iii), (iv), (v) [cf. also the discussion of“possible
```

### Page 182

```text
[10777] 182 SHINICHI MOCHIZUKI
[10778] images” at the beginning of the present proof]. Here, with regard to (IPL), we ob-
[10779] serve that theF⊩▶-prime-strip portion of thelink/relationship of this collection
[10780] of possibilities of output data to theinput data (F⊩▶×μ-)prime-strip [cf. Re-
[10781] mark 3.11.1, (ii)] consists precisely of(full poly-)isomorphisms ofF⊩▶-prime-
[10782] strips, while the corresponding link/relationship forF⊣×μ-prime-strips is some-
[10783] what more complicated, as a result of theindeterminacies (Ind1), (Ind2), (Ind3).
[10784] Also, in this context, we observe that, although the multiradial construction algo-
[10785] rithm of Theorem 3.11 in fact involves the Θ-pilot object at (0,0), in the present
[10786] discussion of Step (xi), we shallonly be concernedwith qualitative logical as-
[10787] pects/consequences of this construction algorithm, i.e., with the
[10788] · input prime-strip link (IPL),
[10789] · simultaneous holomorphic expressibility (SHE),a n d
[10790] · algorithmic parallel transport (APT)
[10791] properties discussed in Remark 3.11.1, (iii), (iv), (v). That is to say, we shall
[10792] take the point of view of “temporarily forgetting” — cf. the discussion of
[10793] hidden internal structures (HIS)in Remark 3.11.1, (iv) — the fact that the
[10794] multiradial construction algorithm of Theorem 3.11 in fact involves Θ-pilot objects,
[10795] theta functions/values, mono-theta environments. Alternatively, in the discussion
[10796] tofollow, weshall, roughlyspeaking, thinkofthemultiradialconstructionalgorithm
[10797] of Theorem 3.11 as
[10798] “some” algorithm that transforms a certain type ofinput data into a
[10799] certain type ofoutput dataand, moreover, satisﬁescertain properties
[10800] (IPL) and (SHE).
[10801] (xi-c) Thus, the discussion of the (IPL) and (SHE) properties in (xi-b) may be
[10802] summarized as follows:
[10803] The multiradial construction algorithm of Theorem3.11 yields a collection
[10804] of possibilities of output data in1,◦U (⊆ 1,◦UQ)t h a ta r elinked/related
[10805] [cf. (IPL)], viaisomorphisms ofF⊩▶-prime-strips, to the representa-
[10806] tion [via thelog-Kummer correspondence in the 1-column] of theq-pilot
[10807] object at (1,0) on1,◦UQ, and, moreover, whose construction may be ex-
[10808] pressed entirely relative to thearithmetic holomorphic structure in
[10809] the 1-column [cf. (SHE)].
[10810] Here, we recall that, in more concrete language, this “arithmetic holomorphic struc-
[10811] ture in the 1-column” amounts, in essence, to thering structure labeled “1,◦”.
[10812] Moreover, by slightly enlarging the collection of possibilities of output data under
[10813] consideration by working with theholomorphic hull 1,◦U (⊇ 1,◦U), we obtain
[10814] output data that is expressed —not i nt e r m so fr e g i o n sc o n t a i n e di nv a r i o u stensor
[10815] products of local ﬁeldslabeled “1,◦” [i.e., more concretely, various isomorphs of
[10816] “Kv”, forv∈ V], but rather — in terms oflocalizations of arithmetic vector
[10817] bundles over certain local ringslabeled “1,◦” [i.e., more concretely, various iso-
[10818] morphs of “OKv”, forv∈ V] — cf. the discussion of Remarks 3.9.5, (vii), (Ob1),
[10819] (Ob2), (Ob5); 3.12.2, (v), below. Such an expression in terms of“localizations of
[10820] arithmetic vector bundles”is necessary in order to render the output data in a form
[10821] that iscomparable to the representation of theq-pilot object [i.e., which arises
[10822] from a certainarithmetic line bundle]a t( 1,0) on1,◦UQ.
```

### Page 183

```text
[10824] INTER-UNIVERSAL TEICHM¨ULLER THEORY III 183
[10825] (xi-d) The discussion of (xi-c) thus yields the following conclusion:
[10826] The multiradial construction algorithmof Theorem 3.11, followed by for-
[10827] mation of theholomorphic hull, yields a collection of possibilities of out-
[10828] put data in1,◦U that arelinked/related [cf. (IPL)], viaisomorphisms
[10829] of F⊩▶-prime-strips, to the representation [via the log-Kummer cor-
[10830] respondence in the 1-column]o ft h eq-pilot object at (1,0) on 1,◦UQ,
[10831] and, moreover, whose construction may be expressed entirely relative to
[10832] localizations of arithmetic vector bundlesover rings that arise in
[10833] the arithmetic holomorphic structurein the 1-column [cf. (SHE)].
[10834] Here, we observe that these “localizations of arithmetic vector bundles” are [unlike
[10835] thearithmetic line bundlethatgivesrisetothe q-pilot object]of rank> 1. Moreover,
[10836] the q-pilot object is deﬁned at the level ofrealiﬁcationsof Frobenioids of [global]
[10837] arithmetic line bundles. Thus, it is only by forming [a suitable positive tensor power
[10838] of] the determinant of the localizations of arithmetic vector bundles mentioned in
[10839] the above display [cf. Remark 3.9.5, (vii), (Ob3), (Ob4)] and then applying the
[10840] [suitably normalized, with respect toj∈| Fl|] log-volume to various regions —
[10841] i.e., theregion1,◦U and theregionthat arises from the representation of theq-pilot
[10842] object at (1,0) on1,◦UQ —i n1,◦UQ [cf. Remark 3.9.5, (vii), (Ob3), (Ob4), (Ob6),
[10843] (Ob7), (Ob9)], that we are able to obtaincompletely comparable objects [cf.
[10844] Remarks 3.9.5, (vii), (Ob5), (Ob6), (Ob7), (Ob8), (Ob9); 3.9.5, (viii), (ix)], namely,
[10845] R≤−|log(Θ)|
[10846] def
[10847] ={λ∈ R| λ≤−| log(Θ)|} ⊆R; −| log(q)|∈ R
[10848] —wherewerecallthat, bydeﬁnition, −|log(Θ)|isthe[ negative—cf. thediscussion
[10849] of “possible images”at the beginning of the present proof] log-volume of1,◦U, while
[10850] −| log(q)| is the log-volume of the region that arises from the representation of
[10851] the q-pilot object at (1,0) on 1,◦UQ. In this context, it is useful to recall from
[10852] Proposition 3.9, (iii) [cf. also the discussion of Remarks 3.9.2, 3.9.6], thatglobal
[10853] arithmetic degrees of objects of global realiﬁed Frobenioids may be interpreted
[10854] as log-volumes [cf. also the discussion of Remarks 1.5.2, (iii); 3.10.1, (iv), as
[10855] well as of Remark 3.12.2, (v), below]. Finally, in this context, we observe [cf.
[10856] the ﬁrst display of the present (xi-d)] that it is ofcrucial importance to apply
[10857] the log-Kummer correspondence in the 1-column [cf. the discussion of log-
[10858] Kummer correspondencesin Remark 3.9.5, (vii), (Ob7), (Ob8); Remark 3.9.5, (viii),
[10859] (sQ4); Remark 3.9.5, (ix); the ﬁnal portion of Remark 3.9.5, (x); the discussion
[10860] of the ﬁnal portion of Remark 3.12.2, (v), below], in order torectify thevertical
[10861] shift/mismatch[cf. thediscussionof(iii), (iv)inthecaseofthe0 -column]between
[10862] the unit portion of 1,0F⊩▶×μ
[10863] ∆ and thelog-shells arising from [the image via the
[10864] relevant Kummer isomorphisms of] this unit portion, which give rise to thetensor
[10865] packets of log-shellsthat constitute1,◦U.
[10866] (xi-e) Next, let us recall that the relationship, i.e., that arises by applying the
[10867] log-volume to the pilot-object, between the pilot-object log-volume −| log(q)|
[10868] ∈ R and theinput data (F⊩▶×μ-)prime-strip is precisely the relationshippre-
[10869] scribed/imposed by thearithmetic holomorphic structurein the 1-column,
[10870] i.e., via the representation of the input data (F⊩▶×μ-)prime-strip on1,◦U relative
```

## IUT IV pp. 27-29: Theorem 1.10 proof Step (iv)-(v)

### Page 27

```text
[01595] INTER-UNIVERSAL TEICHM¨ULLER THEORY IV 27
[01596] Thus, we proceed to estimate this log-volume ateach vQ ∈ VQ. Once one ﬁxesvQ,
[01597] this amounts to estimating the component of this log-volume in
[01598] “IQ(S±
[01599] j+1;n,◦D⊣
[01600] vQ)”
[01601] [cf. the notation of [IUTchIII], Theorem 3.11, (i), (a)], foreach j ∈{ 1,...,l ⋇},
[01602] which we shall also regard as an element ofF⋇
[01603] l , and then computing theaverage,
[01604] over j ∈{ 1,...,l ⋇}, of these estimates. Here, we recall [cf. [IUTchI], Proposition
[01605] 6.9, (i); [IUTchIII], Proposition 3.4, (ii)] thatS±
[01606] j+1 = {0,1,...,j }. Also, we recall
[01607] from [IUTchIII], Proposition 3.2, that “IQ(S±
[01608] j+1;n,◦D⊣
[01609] vQ)” is, by deﬁnition, atensor
[01610] productof j+1 copies, indexed by the elements ofS±
[01611] j+1,o ft h edirect sumof theQ-
[01612] spansofthe log-shellsassociatedtoeachoftheelementsof V(Fmod)vQ [cf., especially,
[01613] the second and third displays of [IUTchIII], Proposition 3.2]. In particular, foreach
[01614] collection
[01615] {vi}i∈S±
[01616] j+1
[01617] of [not necessarily distinct!] elements of V(Fmod)vQ, we must estimate the com-
[01618] ponent of the log-volume in question corresponding to thetensor product of the
[01619] Q-spans of thelog-shells associated to this collection{vi}i∈S±
[01620] j+1
[01621] and then compute
[01622] the weighted average[cf. the discussion of Remark 1.7.1], over possible collections
[01623] {vi}i∈S±
[01624] j+1
[01625] , of these estimates.
[01626] (v) LetvQ ∈ Vdst
[01627] Q . Fix j, {vi}i∈S±
[01628] j+1
[01629] as in Step (iv). Writevi ∈ V
[01630] ∼
[01631] → Vmod =
[01632] V(Fmod) for the element corresponding tovi. We would like to apply Proposition
[01633] 1.4, (iii), to the present situation, by taking
[01634] · “I”t ob eS±
[01635] j+1;
[01636] · “I∗ ⊆ I” to be the set ofi ∈ I such thatevi
[01637] >p vQ −2;
[01638] · “ki”t ob eKvi
[01639] [so “Ri” will be the ring of integersOKvi
[01640] of Kvi
[01641] ];
[01642] · “i†”t ob ej ∈ S±
[01643] j+1;
[01644] · “λ”t ob e0i fvj ∈ Vgood;
[01645] · “λ” to be “ord(−)” of the element qj2
[01646] vj
[01647] [cf. the deﬁnition of “q
[01648] v
[01649] ”i n
[01650] [IUTchI], Example 3.2, (iv)] ifvj ∈ Vbad.
[01651] Thus, theinclusion “φ(pλ · (RI)∼) ⊆ p⌊λ−dI−aI⌋· logp(R×
[01652] I )” of Proposition 1.4,
[01653] (iii), implies that the result of multiplying “p⌊λ⌋−|I| ·2−|I| ·logp(R×
[01654] I )” by a suitable
[01655] nonpositive[cf. theinequalitiesconcerning“ dI+aI”thatconstitutetheﬁnalportion
[01656] of Proposition 1.4, (iii)] integer power ofpvQ containsthe “union of possible images
[01657] ofaΘ-pilotobject”discussedinStep(iv). Thatistosay, the indeterminacies(Ind1)
[01658] and (Ind2) are taken into account by thearbitrarynature of the automorphism “φ”
[01659] [cf. Proposition 1.2], while theindeterminacy (Ind3) is taken into account by the
[01660] fact that we are consideringupper bounds[cf. the discussion of Step (x) of the proof
[01661] of [IUTchIII], Corollary 3.12], together with the fact that the above-mentioned
[01662] integer power of pvQ is nonpositive, which implies that the module obtained by
[01663] multiplying by this power ofpvQ contains “p⌊λ⌋−|I| · 2−|I| · logp(R×
[01664] I )”. Thus, an
[01665] upper bound on the component of the log-volume of theholomorphic hull under
```

### Page 28

```text
[01667] 28 SHINICHI MOCHIZUKI
[01668] consideration may be obtained by computing an upper bound for the log-volume of
[01669] the right-hand side of the inclusion “p⌊λ−dI−aI⌋·logp(R×
[01670] I ) ⊆ p⌊λ−dI−aI⌋−bI ·(RI)∼”
[01671] of Proposition 1.4, (iii). Such anupper bound
[01672] “
[01673] (
[01674] −λ+ dI +1
[01675] )
[01676] ·log(p)+
[01677] ∑
[01678] i∈I∗
[01679] {3+log( ei)}”
[01680] is given in the second displayed inequality of Proposition 1.4, (iii). Here, we note
[01681] that ifevi ≤ pvQ −2 for alli ∈ I, then thisupper boundassumes the form
[01682] “
[01683] (
[01684] −λ+ dI +1
[01685] )
[01686] ·log(p)”.
[01687] On the other hand, by (R4), ifevi
[01688] >p vQ − 2f o rs o m ei ∈ I, then it follows that
[01689] pvQ ≤ e∗
[01690] mod ·l, and log(evi) ≤− 3+4 ·log(e∗
[01691] mod ·l), so theupper boundin question
[01692] may be taken to be
[01693] “
[01694] (
[01695] −λ+ dI +1
[01696] )
[01697] ·log(p)+4 ( j +1) ·l∗
[01698] mod”
[01699] —w h e r ew ew r i t el∗
[01700] mod
[01701] def
[01702] = log(e∗
[01703] mod ·l). Also, we note that, unlike the other terms
[01704] that appear in theseupper bounds,“ λ”i s asymmetric with respect to the choice
[01705] of “i† ∈ I”i n S±
[01706] j+1. Since we would like to computeweighted averages [cf. the
[01707] discussion of Remark 1.7.1], we thus observe that, aftersymmetrizing with respect
[01708] to the choice of “i† ∈ I”i n S±
[01709] j+1,t h i supper boundmay be written in the form
[01710] “β⃗e”
[01711] [cf. the notation of Proposition 1.7] if, in the situation of Proposition 1.7, one takes
[01712] · “E”t ob eV(Fmod)vQ;
[01713] · “n”t ob e j +1 ,s oa ne l e m e n t“⃗e ∈ En” corresponds precisely to a
[01714] collection {vi}i∈S±
[01715] j+1
[01716] ;
[01717] · “λe”, for an elemente ∈ E corresponding tov ∈ V(Fmod)= Vmod,t ob e
[01718] [(Fmod)v : QvQ] ∈ R>0;
[01719] · “βe”, for an elemente ∈ E corresponding tov ∈ V(Fmod)= Vmod,t ob e
[01720] log(dK
[01721] v )− j2
[01722] 2l(j+1) ·log(qv)+ 1
[01723] j+1 ·log(pvQ)+4 ·ιvQ ·l∗
[01724] mod
[01725] — where we recall thatιvQ
[01726] def
[01727] =1i f pvQ ≤ e∗
[01728] mod ·l, ιvQ
[01729] def
[01730] =0i f pvQ >e ∗
[01731] mod ·l.
[01732] Here, we note that it follows immediately from the ﬁrst equality of the ﬁrst dis-
[01733] play of Proposition 1.7 that, after passing toweighted averages, the operation of
[01734] symmetrizing with respect to the choice of “i† ∈ I”i nS±
[01735] j+1 does not aﬀectthe com-
[01736] putation of theupper boundunder consideration. Thus, by applying Proposition
[01737] 1.7, we obtain that the resulting“weighted average upper bound”is given by
[01738] (j +1) ·log(dK
[01739] vQ)− j2
[01740] 2l ·log(qvQ)+log( sQ
[01741] vQ)+4( j +1) ·l∗
[01742] mod ·log(s≤
[01743] vQ)
```

### Page 29

```text
[01745] INTER-UNIVERSAL TEICHM¨ULLER THEORY IV 29
[01746] — where we recall the notational conventions introduced in Step (iii). Thus, it
[01747] remains to compute theaverage overj ∈ F⋇
[01748] l .B y averaging over j ∈{ 1,...,l ⋇ =
[01749] l−1
[01750] 2 } and applying (E1), (E2), we obtain the“procession-normalized upper
[01751] bound”
[01752] (l⋇+3)
[01753] 2 ·log(dK
[01754] vQ)− (2l⋇+1)(l⋇+1)
[01755] 12l ·log(qvQ)+log( sQ
[01756] vQ)+2( l⋇ +3) ·l∗
[01757] mod ·log(s≤
[01758] vQ)
[01759] = l+5
[01760] 4 ·log(dK
[01761] vQ)− l+1
[01762] 24 ·log(qvQ)+log( sQ
[01763] vQ)+( l+5) ·l∗
[01764] mod ·log(s≤
[01765] vQ)
[01766] ≤ l+1
[01767] 4 ·
[01768] {
[01769] (1+ 4
[01770] l )·log(dK
[01771] vQ)− 1
[01772] 6 ·log(qvQ)+ 4
[01773] l ·log(sQ
[01774] vQ)+ 20
[01775] 3 ·l∗
[01776] mod ·log(s≤
[01777] vQ)
[01778] }
[01779] — where, in the passage to the ﬁnal displayed inequality, we apply the estimates
[01780] 1
[01781] l+1 ≤ 1
[01782] l and 4(l+5)
[01783] l+1 ≤ 20
[01784] 3 , both of which may be regarded as consequences of the
[01785] fact thatl ≥ 5.
[01786] (vi) Next, let vQ ∈ Vnon
[01787] Q \ Vdst
[01788] Q . Fix j, {vi}i∈S±
[01789] j+1
[01790] as in Step (iv). Write
[01791] vi ∈ V
[01792] ∼
[01793] → Vmod = V(Fmod) for the element corresponding tovi. We would like to
[01794] apply Proposition 1.4, (iv), to the present situation, by taking
[01795] · “I”t ob eS±
[01796] j+1;
[01797] · “ki”t ob eKvi
[01798] [so “Ri” will be the ring of integersOKvi
[01799] of Kvi
[01800] ].
[01801] Here, we note that our assumption thatvQ ∈ Vnon
[01802] Q \Vdst
[01803] Q implies that the hypotheses
[01804] of Proposition 1.4, (iv), are satisﬁed. Thus, theinclusion “φ((RI)∼) ⊆ (RI)∼”o f
[01805] Proposition 1.4, (iv), implies that the tensor product of log-shells under consider-
[01806] ation contains the “union of possible images of a Θ-pilot object” discussed in Step
[01807] (iv). That is to say, theindeterminacies (Ind1) and (Ind2) are taken into account
[01808] by the arbitrary nature of the automorphism “φ” [cf. Proposition 1.2], while the
[01809] indeterminacy (Ind3) is taken into account by the fact that we are consideringupper
[01810] bounds [cf. the discussion of Step (x) of the proof of [IUTchIII], Corollary 3.12],
[01811] together with the fact that the “container of possible images” isprecisely equalto
[01812] the tensor product of log-shells under consideration. Thus, an upper bound on the
[01813] component of the log-volume under consideration may be obtained by computing
[01814] an upper bound for the log-volume of the right-hand side “(RI)∼” of the above
[01815] inclusion. Such anupper bound
[01816] “0”
[01817] is given in the ﬁnal equality of Proposition 1.4, (iv). One may then compute a
[01818] “weighted average upper bound” a n dt h e na“procession-normalized upper
[01819] bound”, as was done in Step (v). The resulting“procession-normalized upper
[01820] bound” is clearly equal to 0.
[01821] (vii) Next, let vQ ∈ Varc
[01822] Q . Fix j, {vi}i∈S±
[01823] j+1
[01824] as in Step (iv). Write vi ∈
[01825] V
[01826] ∼
[01827] → Vmod = V(Fmod) for the element corresponding to vi. We would like to
[01828] apply Proposition 1.5, (iii), (iv), to the present situation, by taking
[01829] · “I”t ob eS±
[01830] j+1 [so |I| = j +1];
[01831] · “V”t ob eV(Fmod)vQ;
```

---

## Numbered display table (N5 citation anchors)

| id | display (abbreviated) | source line(s) |
|---|---|---|
| D1 | `−|log Θ| ∈ R ⋃ {+∞}` | III:10328 |
| D2 | `−|log q| ∈ R` | III:10342 |
| D3 | `−|log Θ| ≥ −|log q|` | III:10354 |
| D4 | `n,◦U = {n,◦U_{j,vQ}} ⊆ n,◦UQ = {n,◦UQ_{j,vQ}}` (union of possible images) | III:10361-10376 |
| D5 | `n,◦U` = collection of holomorphic hulls of the subsets | III:10388-10404 |
| D6 | `(Ind1)` automorphisms of the procession; `(Ind2)` independent `I_sm` copies on tensor factors | III:9260-9274 |
| D7 | `(Ind3)` upper semi-compatibility: inclusions at `V_non_Q`, surjections at `V_arc_Q` | III:9441-9448 |
| D8 | log-volumes invariant under Ind1/Ind2 and convert Ind3 into an inequality from above | III:10724-10732 |
| D9 | `R_{≤−|log Θ|} := {λ∈R | λ≤−|log Θ|} ⊆ R; −|log q|∈ R` | III:10844-10850 |
| D10 | `|log q| = 1/(2l)·log(q)` (normalization) | IV:1360-1362 |
| D11 | `C_Θ = (l+1)/4·|log q|·{...}−1` | IV:1366-1377 |
| D12 | `1/6·log(q) ≤ ...` final Theorem 1.10 bound | IV:1380-1386 |
| D13 | Step (iv): bound the procession-normalized log-volume of the hull of the union | IV:1587-1593 |
| D14 | inclusion `φ(p^λ·(R_I)∼) ⊆ p^{⌊λ−d_I−a_I⌋}·log_p(R×_I)` | IV:1651-1653 |
| D15 | upper bound `(−λ+d_I+1)·log(p) + ∑_{i∈I*}{3+log(e_i)}` | IV:1671-1680 |
| D16 | weighted average bound `(j+1)log(d^K_vQ) − j²/(2l)log(q_vQ)+...` | IV:1738-1743 |
| D17 | procession-normalized bound `= (l+5)/4 log(d^K_vQ) − (l+1)/24 log(q_vQ)+...` | IV:1751-1765 |
| D18 | final inequality `≤ (l+1)/4·{(1+4/l)log d − 1/6 log q + ...}` | IV:1766-1778 |

All ranges refer to the global line numbers printed in the page blocks above;
OCR source lines are preserved verbatim.
