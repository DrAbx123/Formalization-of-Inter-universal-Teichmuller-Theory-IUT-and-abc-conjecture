import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-!
# §4.4 cor312-to-ABC chain cards and the Explicit Theorem 5.4 shape card

This module freezes, card by card, the reduction chain from the IUT III
Corollary 3.12 boundary to `ABCConjecture` that was fixed in §4.4 of the
estimates survey (`logs/coordination/outsider-survey-estimates-20261016.md`,
lines 236-241), transcribing the statements from

* `papers/motizuki_corpus/text/Explicit estimates in IUTeich.txt`
  (Mochizuki-Fesenko-Hoshi-Minamide-Porowski; cited by text line numbers), and
* `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt`
  for the [IUTchIV] anchors.

Disambiguation: the paper has no subsection numbered 4.4 of its own (its §4
is the mu_6-version of [IUTchI-III]); the "§4.4" of the task is the survey
section just cited.

Card map (paper text line numbers):

* step-1: Theorem 5.1 lines 1630-1739; condition (C2) lines 1889-1894,
  derivation completed lines 2195-2202
* step-2: Corollary 5.2 lines 1794-1894; Proposition 2.2 lines 1078-1123;
  Theorem 5.3, (i) lines 2225-2232
* step-3: Theorem 5.4 lines 2426-2443, proof lines 2444-2513
* step-4: `ABCBridge/Bridge/IUTToABC.lean:29-43` and `:57-79` (repository)
* Thm-5.4 shape: Theorem 5.4 lines 2426-2443; introduction Theorem B
  lines 189-201

Machine-checked content: the five cards (plain data), the typed target shape
`cor312ToABCTargetShape`, which is definitionally the right-hand side of
`abcConjecture_iff_abcArithmeticWeightHeightBound` (`IUTToABC.lean:57`), the
interface theorem `cor312ToABCTargetShape_iff_abcConjecture` obtained by
reusing the accepted equivalence, and the statement-only shape
`explicitEstimatesThm54Shape`.

Nothing here proves the chain or any ABC estimate: chain steps 1-3 remain
cards with their missing object layers recorded, the Theorem 5.4 display is
not proved, and no reduction is claimed.
-/

noncomputable section

namespace LeanFormal.IUT.Cor312ToABCCards

open LeanFormal.IUT
open LeanFormal.IUT.Audit

/-- Paper-fidelity card for one step of the §4.4 cor312-to-ABC chain.  Every
field is transcribed from the cited paper text; `source` carries the document
plus the text line range. -/
structure Cor312ToABCChainCard where
  /-- Card identifier. -/
  id : String
  /-- Citation: document, result number, and text line range. -/
  source : String
  /-- The objects of the frozen statement. -/
  objects : String
  /-- The quantifier order of the frozen statement. -/
  quantifiers : String
  /-- The hypotheses of the frozen statement. -/
  hypotheses : String
  /-- The conclusion of the frozen statement. -/
  conclusion : String
  /-- Which pieces exist in Lean and which are missing. -/
  machineStatus : List String
  /-- Lower cards or obligations this step depends on. -/
  dependsOn : List String
  /-- The consumer of the step. -/
  consumer : String
  /-- Ledger status of the step; `.pending` means card only, not proved. -/
  status : VerificationStatus
  deriving Repr

/-- §4.4 chain step 1: the mu_6-version of the [IUTchIII] Corollary 3.12
situation together with the Theta-pilot log-volume estimate yields condition
(C2).  The step is open; the repository-side wall is the Step-XI hull
log-volume boundary. -/
def cor312ToABCChainStepCor312ToC2Card : Cor312ToABCChainCard :=
  { id := "cor312-to-ABC.step-1"
    source :=
      "Explicit estimates in IUTeich, Theorem 5.1 (lines 1630-1662 statement; line 1717 the " ++
        "bound l >= 10^15; lines 1718-1731 the explicit C_Theta; lines 1733-1739 final " ++
        "display); condition (C2) lines 1889-1894; derivation of (C2) completed lines " ++
        "2195-2202; mu_6-initial Theta-data: Definition 4.1 (line 1318); [IUTchIV] analog " ++
        "Theorem 1.10 (Inter-universal Teichmuller Theory IV.txt:1255)"
    objects :=
      "a collection of mu_6-initial Theta-data (Definition 4.1); the mu_6-version of the " ++
        "[IUTchIII] Corollary 3.12 situation; the Theta-pilot log-volume log(q); the " ++
        "effective arithmetic divisors d^ADiv, q^ADiv, f^ADiv and their log-degrees log(d), " ++
        "log(q), log(f) (lines 1665-1708); F_mod subset F_tpd subset F; the quantities d_mod, " ++
        "e*_mod and the prime l"
    quantifiers :=
      "fix the data; assume the mu_6-Corollary-3.12 situation and good reduction away from " ++
        "2*3*5*l; for l >= 10^15 there exists C_Theta (explicit, lines 1718-1731) such that " ++
        "the display of lines 1733-1739 holds; the same data produce the point x_E whose (C2) " ++
        "inequality is the display of lines 1889-1894"
    hypotheses :=
      "F = F_mod(sqrt(-1), E_{F_mod}[2*3*5]) = F_tpd(sqrt(-1), E_{F_tpd}[3*5]) with the " ++
        "(3*5)-torsion defined over F (lines 1650-1662); good reduction at every " ++
        "nonarchimedean place not dividing 2*3*5*l (lines 1634-1635); l >= 10^15 (line 1717)"
    conclusion :=
      "(1/6)*log(q) <= (1 + 20*d_mod/l)*(log(d_F_tpd) + log(f_F_tpd)) + 4.0881*e*_mod*l <= " ++
        "(1 + 20*d_mod/l)*(log(d_F) + log(f_F)) + 4.0881*e*_mod*l (lines 1733-1739); " ++
        "equivalently the (C2) inequality (1/6)*log(q-forall) <= (1 + eps)*(log-diff_X(x_E) + " ++
        "log-cond_D(x_E)) (lines 1889-1894)"
    machineStatus :=
      [ "present: the Theta-pilot hull/finiteness interface IQHullLogVolumeInterface of " ++
          "IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean " ++
          "(hull_logVolume_lt_top proved) and the conditional assembly of " ++
          "ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean",
        "missing: mu_6-initial Theta-data (Definition 4.1); the mu_6-version of Corollary " ++
          "3.12; the Theta-pilot log-volume object; the explicit C_Theta constant layer; the " ++
          "arithmetic divisor/degree layer of [IUTchIV] Definition 1.9" ]
    dependsOn :=
      [ "IUT-III.cor312-to-ABC",
        "Step-XI hull log-volume wall (still unclosed)" ]
    consumer :=
      "cor312ToABCChainStepExcToBDBoundCard; Cor312ToABCBridgeInterface.lean"
    status := VerificationStatus.pending }

/-- §4.4 chain step 2: condition (C2) together with the exclusion of the
finite exceptional set (explicit prime number theorem, Proposition 2.2)
yields the Corollary-2.3-type bounded-discrepancy inequality, i.e. the
display of Theorem 5.3, (i).  Paper-internal; here a landing card. -/
def cor312ToABCChainStepExcToBDBoundCard : Cor312ToABCChainCard :=
  { id := "cor312-to-ABC.step-2"
    source :=
      "Explicit estimates in IUTeich, Corollary 5.2 (lines 1794-1894; exceptional sets " ++
        "lines 1837-1855; (C2) lines 1889-1894); Proposition 2.2 explicit PNT (lines " ++
        "1078-1123); Theorem 5.3 (lines 2203-2237), statement (i) lines 2225-2232 with proof " ++
        "anchor lines 2238-2242; dictionary Remark 1.10.1 (lines 885-896); [IUTchIV] analog " ++
        "Corollary 2.3 (Inter-universal Teichmuller Theory IV.txt:3117)"
    objects :=
      "the finite exceptional sets Exc^{kappa,d,eps} and Exc^{mcx}_{d,eps} (lines " ++
        "1837-1843); the point x_E over a mono-complex field and log(q-forall); the " ++
        "normalized log-different log-diff_X and log-conductor log-cond_D (lines 1892-1894); " ++
        "the height terms h_non(j(E_{a,b,c})), H_L, Delta_L, rad_L(a,b,c) of Theorem 5.3 " ++
        "(lines 2210-2219)"
    quantifiers :=
      "d in Z_{>0}; eps in R_{>0} cap R_{<=1}; there exists a finite exceptional set " ++
        "depending only on (d, eps) (mono-complex version) containing the points whose " ++
        "elliptic curves have automorphisms of order > 2; for every elliptic curve that lifts " ++
        "to a point x_E in U_X(F) cap U_X(Q)^{<=d} cap U_X(Q)^{mcx} outside the set the " ++
        "display holds"
    hypotheses :=
      "E_F determines a Q-valued point of the moduli stack lifting to x_E as above; the " ++
        "(3*5)-torsion is defined over F; F = F_mod(sqrt(-1), E[2*3*5]); (C2) holds at x_E; " ++
        "explicit PNT inputs: pi(x) <= 1.022*x/log(x) for x >= 5*10^20 and |theta(x) - x| <= " ++
        "0.00071*x for x >= 10^15 (lines 1092-1097)"
    conclusion :=
      "(1/6)*h_non(j(E_{a,b,c})) <= max{(1/d)*(1 + eps)*log(Delta_L*rad_L(a,b,c)), " ++
        "(1/6)*h_d(eps)} <= (1/d)*(1 + eps)*log(Delta_L*rad_L(a,b,c)) + (1/6)*h_d(eps) " ++
        "(Theorem 5.3, (i), lines 2225-2232) - the Corollary-2.3-type bounded-discrepancy " ++
        "inequality, via the dictionary of Remark 1.10.1 (normalized degree of the " ++
        "q-parameter divisor = h_non(j(E)))"
    machineStatus :=
      [ "present: the radical and real-exponential layers " ++
          "(Foundations/Arithmetic/Radical.lean, ABCBridge/Statement.lean, Mathlib Real.exp and " ++
          "rpow)",
        "missing: the moduli stack (Mell)_Q; the compactly bounded sets K_V; the exceptional " ++
          "sets; the normalized log-diff and log-cond functions; h_non(j(E)); H_L, Delta_L, " ++
          "rad_L; the explicit PNT estimates" ]
    dependsOn :=
      [ "cor312-to-ABC.step-1",
        "explicit-estimates.Prop-2.2" ]
    consumer :=
      "cor312ToABCChainStepMonoComplexToSzpiroCard; Theorem 5.3, (ii) display"
    status := VerificationStatus.pending }

/-- §4.4 chain step 3: the Q-specialization of the mono-complex inequality
(with the Legendre denominator x + a/c and the Remark 1.10.1 dictionary)
yields the explicit Szpiro shape of Theorem 5.4. -/
def cor312ToABCChainStepMonoComplexToSzpiroCard : Cor312ToABCChainCard :=
  { id := "cor312-to-ABC.step-3"
    source :=
      "Explicit estimates in IUTeich, Theorem 5.4 (lines 2426-2443), proof lines 2444-2513 " ++
        "(Claims 5.4A-C lines 2445-2500; Q-specialization lines 2503-2510; cube step lines " ++
        "2511-2512); introduction Theorem B lines 189-201; dictionary Remark 1.10.1 lines " ++
        "885-896"
    objects :=
      "nonzero coprime integers a, b, c with a + b + c = 0; eps in R with 0 < eps <= 1; " ++
        "|abc| = ||abc||_C; rad(abc) the product of the primes dividing abc; the " ++
        "Legendre-form curve E_{a,b,c}: y^2 = x(x-1)(x + a/c); H_L, Delta_L, rad_L of Theorem " ++
        "5.3 (lines 2210-2219); the archimedean value |abc^{-2}|_w"
    quantifiers :=
      "for all a b c in Z minus {0}, pairwise coprime, with a + b + c = 0; for all eps in R " ++
        "with 0 < eps <= 1"
    hypotheses :=
      "a, b, c nonzero pairwise coprime integers with a + b + c = 0; eps a positive real " ++
        "number <= 1"
    conclusion :=
      "|abc| = ||abc||_C <= 24*max{exp(1.7*10^30*eps^{-166/81}), (rad(abc))^{3(1+eps)}} <= " ++
        "24*exp(1.7*10^30*eps^{-166/81})*(rad(abc))^{3(1+eps)} (lines 2432-2433)"
    machineStatus :=
      [ "present: the statement-only shape explicitEstimatesThm54Shape of this file",
        "missing: h_non(j(E)) and h_tor_non; H_L, Delta_L, rad_L; the Claims 5.4A-C " ++
          "bookkeeping; the cube step" ]
    dependsOn := [ "cor312-to-ABC.step-2" ]
    consumer :=
      "explicitEstimatesThm54ShapeCard; cor312ToABCChainStepInterfaceToABCCard"
    status := VerificationStatus.pending }

/-- §4.4 chain step 4: the interface link from the frozen target shape to
`ABCConjecture`, closed by reuse of the accepted equivalence of
`IUTToABC.lean:57`.  Only this shape-level link is closed; the upstream steps
remain cards and no ABC estimate is proved. -/
def cor312ToABCChainStepInterfaceToABCCard : Cor312ToABCChainCard :=
  { id := "cor312-to-ABC.step-4"
    source :=
      "ABCBridge/Bridge/IUTToABC.lean:29-43 (abcConjecture_iff_abcLogConjecture) and :57-79 " ++
        "(abcConjecture_iff_abcArithmeticWeightHeightBound); this file: " ++
        "cor312ToABCTargetShape and cor312ToABCTargetShape_iff_abcConjecture"
    objects :=
      "the target shape cor312ToABCTargetShape (the right-hand side of " ++
        "IUTToABC.lean:57-62); the repository statements ABCConjecture, ABCLogConjecture and " ++
        "the height/weight dictionary Height.logHeight_1, abcRationalPoint, arithmeticWeight"
    quantifiers :=
      "for every eps > 0 there exists A; for every ABC triple in the Nat dictionary " ++
        "(IsABCTriple): logHeight_1(abcRationalPoint a c) <= (1 + " ++
        "eps)*arithmeticWeight(abcRationalPoint a c) + A"
    hypotheses :=
      "none beyond the quantified ones: the equivalence is unconditional and assumes no ABC " ++
        "estimate on either side"
    conclusion :=
      "cor312ToABCTargetShape <-> ABCConjecture (proved in this file by reuse of the " ++
        "accepted equivalence); the shape-level interface of the chain is closed while steps " ++
        "1-3 stay cards"
    machineStatus :=
      [ "proved: cor312ToABCTargetShape_iff_abcConjecture (reuse of the accepted equivalence)",
        "unchanged: the pending obligation cor312ToABCBridge of IUTToABC.lean:9 (not reformed " ++
          "here)" ]
    dependsOn := [ "accepted: ABCBridge/Bridge/IUTToABC.lean:57-79" ]
    consumer :=
      "the pending cor312ToABCBridge obligation; ABCConjecture interface"
    status := VerificationStatus.interface }

/-- The frozen target shape of the chain: definitionally the right-hand side
of `abcConjecture_iff_abcArithmeticWeightHeightBound`
(`ABCBridge/Bridge/IUTToABC.lean:57-62`).  Naming this shape proves nothing
about it; the theorem below only re-exposes the accepted equivalence. -/
def cor312ToABCTargetShape : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ A : ℝ,
    ∀ a b c : ℕ, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A

/-- The interface theorem of §4.4 chain step 4: the frozen target shape is
equivalent to `ABCConjecture`.  Proof by reuse of the accepted equivalence
`abcConjecture_iff_abcArithmeticWeightHeightBound`; this proves nothing about
the IUT-side chain steps 1-3. -/
theorem cor312ToABCTargetShape_iff_abcConjecture :
    cor312ToABCTargetShape ↔ ABCConjecture :=
  abcConjecture_iff_abcArithmeticWeightHeightBound.symm

/-- The constant `exp(1.7*10^30*eps^{-166/81})` of Theorem 5.4 (line 2432),
frozen exactly as printed. -/
def explicitEstimatesThm54ExpConstant (epsilon : ℝ) : ℝ :=
  Real.exp (1.7e30 * epsilon ^ (-(166 / 81 : ℝ)))

/-- The middle term `24*max{exp(1.7*10^30*eps^{-166/81}),
(rad(abc))^{3(1+eps)}}` of Theorem 5.4 (line 2432); `radicalProduct` is the
value of `rad(abc)`. -/
def explicitEstimatesThm54MaxBound (radicalProduct : ℕ) (epsilon : ℝ) : ℝ :=
  24 * max (explicitEstimatesThm54ExpConstant epsilon)
    ((radicalProduct : ℝ) ^ (3 * (1 + epsilon)))

/-- Statement-only shape of Theorem 5.4 (lines 2426-2443) over `ℤ`: nonzero
pairwise coprime integers with `a + b + c = 0`, `eps` positive and at most
`1`, and the display `|abc| <= 24*max{...} <= 24*exp(...)*rad(abc)^{3(1+eps)}`.
Under `ℤ ⊆ ℂ` the paper's `|abc| = ||abc||_C` is `(a*b*c).natAbs`, and the
paper's `rad(abc)` is the radical of that natural number.  This is a
statement card: no proof of the display is provided here. -/
def explicitEstimatesThm54Shape : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    IsCoprime a b → IsCoprime b c → IsCoprime c a → a + b + c = 0 →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
        ((a * b * c).natAbs : ℝ) ≤
            explicitEstimatesThm54MaxBound (radical ((a * b * c).natAbs)) epsilon ∧
          explicitEstimatesThm54MaxBound (radical ((a * b * c).natAbs)) epsilon ≤
            24 * (explicitEstimatesThm54ExpConstant epsilon *
              ((radical ((a * b * c).natAbs) : ℝ) ^ (3 * (1 + epsilon))))

/-- Shape card of the Explicit-estimates Theorem 5.4 (effective Szpiro),
frozen as `explicitEstimatesThm54Shape`; the typed shape is a statement and
carries no proof. -/
def explicitEstimatesThm54ShapeCard : Cor312ToABCChainCard :=
  { id := "explicit-estimates.Thm-5.4"
    source :=
      "Explicit estimates in IUTeich, Theorem 5.4 (lines 2426-2443); introduction Theorem B " ++
        "(lines 189-201); general mono-complex form Theorem A, (ii) (lines 184-188); frozen " ++
        "shape: explicitEstimatesThm54Shape of this file"
    objects :=
      "same objects as step 3: a, b, c nonzero coprime integers with a + b + c = 0; eps in " ++
        "(0,1]; |abc| = ||abc||_C; rad(abc); the constants 1.7*10^30 and 166/81 exactly as " ++
        "printed"
    quantifiers :=
      "for all a b c in Z minus {0}, pairwise coprime, with a + b + c = 0; for all eps in R " ++
        "with 0 < eps <= 1"
    hypotheses :=
      "a, b, c nonzero pairwise coprime integers with a + b + c = 0 (the repository Nat " ++
        "dictionary reads ABC triples as 0 < a, 0 < b, a + b = c, coprime, so that (a, b, -c) " ++
        "is the Z-form); eps positive and at most 1"
    conclusion :=
      "explicitEstimatesThm54Shape, i.e. |abc| <= 24*max{exp(1.7*10^30*eps^{-166/81}), " ++
        "(rad(abc))^{3(1+eps)}} <= 24*exp(1.7*10^30*eps^{-166/81})*(rad(abc))^{3(1+eps)}"
    machineStatus :=
      [ "present: the typed statement explicitEstimatesThm54Shape (no proof)",
        "missing: h_non(j(E)) and h_tor_non; H_L, Delta_L, rad_L; the Claims 5.4A-C " ++
          "bookkeeping; the cube step" ]
    dependsOn := [ "cor312-to-ABC.step-3" ]
    consumer :=
      "cor312ToABCChainStepInterfaceToABCCard; future effective-ABC transfer (not formalized)"
    status := VerificationStatus.pending }

/-- The five cards of this pack in chain order, with the Theorem 5.4 shape
card last. -/
def cor312ToABCCardRegistry : List Cor312ToABCChainCard :=
  [ cor312ToABCChainStepCor312ToC2Card,
    cor312ToABCChainStepExcToBDBoundCard,
    cor312ToABCChainStepMonoComplexToSzpiroCard,
    cor312ToABCChainStepInterfaceToABCCard,
    explicitEstimatesThm54ShapeCard ]

end LeanFormal.IUT.Cor312ToABCCards

namespace LeanFormal.IUT.Audit

/-- Audit record for this card pack.  The chain steps 1-3 and the Theorem 5.4
display are cards only; the interface step 4 is closed by reuse of the
accepted equivalence.  No reduction and no ABC estimate is claimed. -/
def cor312ToABCChainCardsObligation : Obligation :=
  { id := "IUT-III.cor312-to-ABC-chain-cards"
    source :=
      "Explicit estimates in IUTeich, Theorem 5.1 (lines 1630-1739), Corollary 5.2 (lines " ++
        "1794-1894), Proposition 2.2 (lines 1078-1123), Theorem 5.3 (lines 2203-2237), " ++
        "Theorem 5.4 (lines 2426-2443); introduction Theorems A/B (lines 153-201); survey " ++
        "section 4.4 (logs/coordination/outsider-survey-estimates-20261016.md, lines 236-241)"
    status := VerificationStatus.pending
    note :=
      "The 4.4 cor312-to-ABC chain is frozen as five cards (four chain steps plus the " ++
        "Theorem 5.4 shape card) with objects, quantifiers, hypotheses, conclusions and text " ++
        "line ranges.  The typed target shape cor312ToABCTargetShape mirrors the right-hand " ++
        "side of IUTToABC.lean:57, and the interface theorem " ++
        "cor312ToABCTargetShape_iff_abcConjecture is proved by reuse of the accepted " ++
        "equivalence.  Chain steps 1-3, the Theorem 5.4 display and the classical " ++
        "Szpiro-to-ABC transfer are not proved; the missing object layers are recorded in " ++
        "each card."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC",
        "IUT-III.cor312-to-ABC-conditional-interface" ] }

/-- Machine-readable landing marker for the explicit PNT input referenced by
the chain-step-2 card (`cor312ToABCChainStepExcToBDBoundCard`): Proposition
2.2 of Explicit estimates in IUTeich, lines 1078-1123.  No explicit PNT
bound (or theta/Chebyshev layer) is formalized in this repository; this
registers only the exact id so the card dependency is machine-resolvable. -/
def explicitEstimatesProp22Obligation : Obligation :=
  { id := "explicit-estimates.Prop-2.2"
    source :=
      "Explicit estimates in IUTeich, Proposition 2.2 (lines 1078-1123): " ++
        "eta_prm = 5*10^20, xi_prm = 10^15, pi(x) <= 1.022*x/log x, " ++
        "|theta(x) - x| <= 0.00071*x"
    status := VerificationStatus.pending
    note :=
      "Not formalized: no explicit PNT bound and no theta/Chebyshev layer exist " ++
        "in this repository; the covering text of IUTIV/Estimates/Section2.lean:13-19 " ++
        "records the same gap.  Registration only; no statement is proved." }

end LeanFormal.IUT.Audit
