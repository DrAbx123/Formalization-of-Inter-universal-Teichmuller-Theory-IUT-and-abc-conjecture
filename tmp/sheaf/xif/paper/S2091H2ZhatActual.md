# S2091: H²(G_v, μ̂^Z) = Ẑ — external local CFT port and the S2036 (M3) reduction

Date: 2026-11-02.  Workspace: D:\lean.  Owner package: S2091.
Deliverable: tmp/sheaf/xif/paper/S2091H2ZhatActual.lean (+ this report).

## 0. Result in one line

The external local class field theory formalization contains the theorem
H²(K, Ẑ(1)) ≃ Ẑ (with Br(k_v) = ℚ/ℤ and the cyclotomic rigidity
H²(K, μ_n) ≃ ℤ/n), and it was **ported and compiled** against the project's
mathlib; the deliverable transports it to the project's actual local field
ℚ_p and proves that S2036's (M3) `PsiCnsH2Normalization p` is *equivalent* to
one explicitly named comparison of cochain models.  The unconditional
inhabitant is NOT obtained: the comparison is genuine mathematics not present
in either formalization.

## 1. Question

S2036 records the (M3) layer of [AbsTopIII], Corollary 1.10, (b), as

    PsiCnsH2Normalization p := Nonempty (PsiCnsH2 p ≃* Multiplicative Zhat)

(tmp/sheaf/xif/paper/S2036ActualPsiCnsM234Actual.lean, lines 380-391), where
PsiCnsH2 p = ContinuousH2 (PsiCnsCoefficientAction p) is the continuous H² of
Gv p = Gal(Qbar_p/Q_p) with coefficients in the actual cyclotome
PsiCnsCyclotome p = Hom(ℚ/ℤ, (O^tri)^x), built from all continuous cochains.
S2046's (M4) consumes the resulting normalization
(tmp/sheaf/xif/paper/S2046PsiCnsActionActual.lean: S2046M4NormalizationRequired,
S2046M4_of_cor110b).

## 2. Inventory of the external repository

tmp/local-cft-port/local-class-field-theory-main (106 Lean files, no
sorry/admit/axiom anywhere in the tree — verified by a full scan), with
dependency tmp/local-cft-port/continuous-kummer-theory-main.  The (M3)-relevant
content is complete:

| file:line | declaration |
|---|---|
| Brauer/ContH2.lean:163 | ContH2 G M — continuous (locally constant) cochain H², functoriality, injective inflation |
| Brauer/KummerH2.lean:35 | H2Mu K Ω n = ContH2 (Gal(Ω/K)) (μ_n) |
| Brauer/KummerH2.lean:61 | toBr_injective — Kummer sequence in degree 2 |
| Brauer/KummerH2.lean:109 | mem_range_toBr_iff — image of H²(K,μ_n) → Br(K) is the n-torsion |
| Brauer/KummerH2.lean:284 | h2MuEquiv : H²(K, μ_n) ≃* ℤ/n (cyclotomic rigidity) |
| Brauer/Invariant.lean:236 | invEquiv : Br(K) ≃* ℚ/ℤ (the invariant map) |
| Brauer/CorBr.lean:75,120 | corBr, invEquiv_corBr |
| Brauer/ArtinPairing.lean | LocChar, pairing, artinChar, pairing_eq_artinChar (Artin pairing = reciprocity) |
| Brauer/H2ZHat.lean:40,134 | H2ZHatOne K Ω = lim_n H²(K, μ_n) along ζ ↦ ζ^(m/n); **h2ZHatOneEquiv : H2ZHatOne K Ω ≃* Ẑ** |
| Brauer/H2ZHat.lean:142 | h2ZHatOneEquiv_res — restriction is multiplication by the degree |
| Galois/ZHat.lean:36 | ZHat = lim_n ℤ/n, intToZHat, zhatPow |
| ClassFieldAxiom/Axiom.lean:191 | the class field axiom, *proved* via Herbrand quotients + Hilbert 90 (no axiom) |

So: yes, the repo contains the Brauer/H² computation, the continuous
cohomology model, and the Artin pairing/corestriction material.  The key
theorem `PadicField.h2ZHatOneEquiv` has axiom set exactly
{propext, Classical.choice, Quot.sound} (checked separately).

## 3. What was built (port record)

Import closure of LocalClassFieldTheory.Brauer.H2ZHat: **74 modules**
(66 LocalClassFieldTheory + 8 ContinuousKummerTheory).  All 74 oleans are
present in the project library D:\lean\.lake\build\lib\lean.  68 were compiled in
this session against untouched upstream sources (one `lean` invocation per
module): 67 with EXIT=0 records in _s2091_final.tsv, plus Galois.ZHat compiled
in the first environment test.  The other 6 (ContinuousKummerTheory.Kummer.*)
were already present from the earlier S2053/S2054 port sessions and were used
as-is.  Build records: tmp/local-cft-port/_s2091_final.tsv
(module, EXIT, seconds, olean bytes, olean SHA256, source SHA256);
compiler logs: tmp/local-cft-port/_s2091_logs/.

Command per module:

    lean -DmaxHeartbeats=4000000 --root <repo-root> \
         -o D:\lean\.lake\build\lib\lean\<Module>.olean <Module>.lean

(`-DmaxHeartbeats=4000000` is needed for
Reciprocity/LevelNeukirch.lean:82, which times out at the default 200000
heartbeats on this machine; no source file was modified — the recorded
SRC_SHA256 are those of the untouched upstream files.)

Key oleans:

    Brauer/H2ZHat.olean      536656 bytes  BF33C4A3C0A028416FC5871E473F48819DD320CE525B59EF63EAC080F13BB76F
    Brauer/KummerH2.olean    972464 bytes  11463718A19C08437DDC69825CE8ECDCC95C49C01DB4725ABA142A648C1B63E2
    Brauer/Invariant.olean   989856 bytes  1AFDFADAA47A393AC1295A8F123A9800A0D6598A7159522B1AE7F8B3CAD2A966
    Brauer/Duality.olean    1930984 bytes  A03A5F23D44C82FE456A86CC74DF22EE966DFA12DF5498FF37E3F8B945E26D80
    Brauer/KummerCompat.olean 558768 bytes 3926C542796F8906131DFCE1097E443ACACDE6CEA44B13C38F7FF7D6468F250B
    Galois/ZHat.olean        489416 bytes  0963C0E008F7604568619CDF5CD2A9CE922F49E1F845A387F6D670AB59AD4A0A

## 4. The deliverable file

tmp/sheaf/xif/paper/S2091H2ZhatActual.lean (module
tmp.sheaf.xif.paper.S2091H2ZhatActual):

    EXIT=0   olean 123960 bytes
    olean SHA256 CB1D195CF19F5E96F76BDFBB43D6F11B3CCB361A240F6D9BD8B8AA3592B42715
    source SHA256 (final) recorded with the handoff message

Theorems (all with axiom set {propext, Classical.choice, Quot.sound}):

1. zhatMulEquivBrauer : Multiplicative Zhat ≃* Multiplicative Brauer.ZHat
   (the two Ẑ models are definitionally equal types; axioms: propext, Quot.sound).
2. gv_eq_absoluteGalois :
   Gv p = (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])   (rfl).
3. brEquivQZ : Br(ℚ_p) ≃* ℚ/ℤ  (the port's invariant map at the project's field).
4. h2MuEquiv_actual : H²(ℚ_p, μ_n) ≃* ℤ/n  (cyclotomic rigidity at the project's field).
5. h2ZHatOneEquiv_of_port :
   H2ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p]) ≃* Multiplicative Zhat
   — the ported H²(ℚ_p, Ẑ(1)) = Ẑ, plus the projection formula
   h2ZHatOneEquiv_of_port_apply (the n-th component is h2MuEquiv of the
   n-th projection).
6. PsiCnsH2LimitComparison p (the named missing comparison) and
   PsiCnsH2Normalization_of_limitComparison : comparison → (M3);
   limitComparison_of_PsiCnsH2Normalization : (M3) → comparison;
   PsiCnsH2Normalization_iff_limitComparison : the comparison is *equivalent*
   to (M3).
7. Cor110bLayersMissing_of_M2_of_comparison_of_M4 :
   (M2) + comparison + (M4) ⇒ the three layers of [AbsTopIII] Cor. 1.10, (b).

## 5. The precise first missing

    PsiCnsH2LimitComparison p :=
      Nonempty (PsiCnsH2 p ≃* Brauer.H2ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p]))

By PsiCnsH2Normalization_iff_limitComparison this is *exactly* (M3): the
remaining content is the comparison of the two cochain models.  Concretely,
three unformalized steps:

(G1) Coefficients.  PsiCnsCyclotome p = Hom(ℚ/ℤ, (O^tri)^x) with the pointwise
     (compact, profinite) topology is, as a topological G_v-module, the inverse
     limit lim_n μ_n of the finite root-of-unity groups used by the port.  The
     project proves Hom(ℚ/ℤ,(O^tri)^x) ≅ Hom(ℚ/ℤ,μ) (S2000) and
     torsion(O^tri)^x ≅ ℚ/ℤ (LocalTorsionCyclotome), but the equivariant limit
     identification is not formalized.

(G2) Cochains.  S2036 forms Z²/B² with *all continuous* functions G × G → the
     compact cyclotome; the port forms the level groups Z²(G,μ_n)/B²(G,μ_n) with
     *locally constant* cochains and then the inverse limit.  One needs
     Z²_cont(G_v, lim μ_n) ≅ lim Z²(G_v, μ_n) (each continuous 2-cocycle into the
     limit is "levelwise locally constant", and conversely) and the matching
     statement for coboundaries: a compatible family of level coboundary
     conditions must lift to one continuous 1-cochain.

(G3) lim¹.  That lift is the vanishing lim¹_n H¹(G_v, μ_n) = 0, which holds
     because each H¹(G_v, μ_n) is finite (μ_n finite, G_v profinite).  No
     Mittag-Leffler/lim¹ theorem for this situation exists in mathlib, in the
     project, or in the external repository.

None of (G1)-(G3) is assumed in the deliverable: PsiCnsH2LimitComparison is a
named proposition, and the equivalence shows the reduction loses nothing.

## 6. Status (project reporting vocabulary)

* statement_compiles: **yes** — EXIT=0, olean 123960 bytes
  SHA256 CB1D195CF19F5E96F76BDFBB43D6F11B3CCB361A240F6D9BD8B8AA3592B42715.
* proof_body_checked: **yes** — no sorry/admit/axiom in the deliverable; the
  kernel checked every proof; the ported modules are compiled (their proofs are
  kernel-checked by Lean at compile time, no sorry in the upstream tree).
* kernel_closed: **yes for the deliverable's theorems** — axiom sets are exactly
  {propext, Classical.choice, Quot.sound} (and zhatMulEquivBrauer only
  {propext, Quot.sound}), printed by #print axioms (log:
  tmp/sheaf/xif/paper/S2091H2ZhatActual.out).
* target_accepted: **NO for the unconditional (M3) target**.  PsiCnsH2Normalization p
  is not inhabited unconditionally; that is precisely the open comparison.  What
  is accepted is (i) the *ported theorem* H²(ℚ_p, Ẑ(1)) ≃ Ẑ, and (ii) the
  equivalence (M3) ↔ comparison together with the conditional reduction.

## 7. Next executable step

Prove (G2)+(G3) in abstract form: for G profinite and (M_n) an inverse system of
finite discrete G-modules with compatible transition maps,

    ContH2 G (lim M_n) ≃* lim_n ContH2 G M_n,

("project to level n" / "lift a compatible family of locally constant
cocycles"), then identify PsiCnsCyclotome p with lim μ_n via (G1).  The first
sub-lemma is that a continuous map from a compact totally disconnected space to
a discrete space is locally constant; mathlib has no lemma for this generality.
