# S2032: the paper's O^▷(A) ⊆ O^◃(A) generator field on the actual local O^◃,
its realified value -|log q|, and the R6 proper link

Date: 2026-11-02 (Asia/Shanghai).  File:
tmp/sheaf/xif/paper/S2032R6GeneratorActual.lean (723 lines).
Consumer: S1979's PilotedFTimesMuPrimeStrip / R6 proper, via S1968's
paperQPilotDivisor and S1978's actual local O-carrier.

## Verdict

**Constructed (EXIT=0, kernel-checked, no `sorry»)** for the generator field on
the actual local O^◃ monoid and the actual local O^× submonoid, for the actual
q_v element, for its realified value -|log q|, and for the R6 proper link at the
piloted level.  **Exact first missing, proved** for the two obstructions that
delimit it (the actual O^× carrier cannot carry q_v; the actual local O^◃ strip
cannot itself be the unpiloted R6 paper side).

## What S1979 left

S1979 constructed the extension `PilotedFTimesMuPrimeStrip» (IUT II, Def. 4.9,
(viii)) and closed R6 at the piloted level, but its generator was the real
number `-|log q_v|» (`qPilotGenerator D b : SourceHaarActualValueMonoid»), not an
element of an actual local O-monoid, and its module docstring recorded exactly
that: "Lift PilotedFTimesMuPrimeStrip's generator field to the paper's actual
O^▷(A) subset O^◃(A) at a universal covering pro-object and prove its realified
value is the q_v scalar."

S1978 supplies the actual local O^× carrier `LocalOFieldUnits p =
(Integers (AlgebraicClosure ℚ_[p]))^×» with its actual Galois action and
norm-log degree, but O^× is a *unit* carrier: every integral unit has norm 1,
so its degree is trivial, while the paper's q_v is a non-unit integral element
(q_v ∈ O^◃, IUT I, §3: `q_v ∈ O^◃(T_X) ≅ O^◃_{K_v}»).

## Constructed (all kernel-checked, no sorry)

1. **The actual local O^◃ monoid and the O^× ⊆ O^◃ submonoid** (section 1):
   `LocalOFieldIntegral p = {x : AlgebraicClosure ℚ_[p] | ‖x‖ ≤ 1 ∧ x ≠ 0}», the
   monoid of nonzero integral elements of the actual local field, with the actual
   O^× inclusion `localOFieldUnitsToIntegral», proved injective
   (`localOFieldUnitsToIntegral_injective»).  S1978's unit carrier is a genuine
   submonoid of the paper's O^◃.
2. **The actual local q_v and the O^▷-generator** (section 2):
   `localOFieldFive = 5 ∈ O^◃» (the generator of the local value monoid
   O^◃/O^× ≅ N in this model; `localOFieldFive_realified»: its realified value is
   `-log 5»), and `localOFieldQParameter D b = 5 ^ order_b ∈ O^◃», proved
   nonzero, non-unit, equal to `localOFieldFive ^ paperQVOrder D b», and with
   p-adic norm literally the paper's q_v: `‖q_v‖ = paperQV D b»
   (`localOFieldQParameter_norm», via S1527's q_v = (1/5)^order_b).  In
   particular q_v is not an integral unit
   (`localOFieldQParameter_not_unit_norm»), so it cannot live in S1978's O^×.
3. **The actual realified value map ρ_v** (section 3):
   `localOFieldNormLog p : O^◃ →* Multiplicative ℝ», the actual norm-log, proved
   nonpositive on O^◃, with
   `ρ_v(q_v) = qPilotGeneratorValue D b = log(paperQV D b) = -|log q|»
   (`localOFieldNormLog_qParameter»).  This is the {ρ_w} of IUT II, Def. 4.9,
   (viii).
4. **The actual local O^◃ F-prime-strip and the piloted strip** (section 4):
   `localOFieldIntegralStrip» (value monoid the actual O^◃, group the actual
   local absolute Galois group, action the actual Galois action on integral
   elements, degree the actual norm-log), its canonical times-mu lift, and
   `localOFieldPilotedStrip D : PilotedFTimesMuPrimeStrip PaperV badPlaces» with
   `generator b = localOFieldQParameter D b» — an actual local O^◃ element, not a
   real number.  Proved:
   * `pilotGeneratorRealifiedValue (localOFieldPilotedStrip D) b =
     qPilotGeneratorValue D b = log (paperQV D b) = -|log (paperQV D b)|»
     (`localOFieldPilotedStrip_value», `_value_eq_log», `_value_eq_neg_abs»);
   * `HasNegativePilotGenerator» (negative arithmetic degree);
   * `associatedPilotObject D (localOFieldPilotedStrip D) = paperQPilotDivisor D»
     — the IUT II, Def. 4.9, (viii) computation on the actual generator gives
     S1968's actual q-pilot divisor.
5. **R6 proper link** (section 5): the R6-proper paper strip and the actual local
   O^◃ strip carry the same actual q_v generator data
   (`HasActualQVGenerator»).  Proved:
   * `paperQPilotPilotedStrip_hasActualQVGenerator» — S1979's paper strip's
     generator value is the realified value of the actual local q_v element;
   * `associatedPilotObject_eq_of_actualQVGenerator» — any piloted strip carrying
     that data computes `paperQPilotDivisor D»;
   * `s2032_r6_proper» — the actual realified value is -|log q|,
     `R6Proper D (paperQPilotPilotedStrip D)» holds (S1979's piloted
     identification), the paper strip has the actual q_v data, and both strips
     compute `paperQPilotDivisor D»;
   * `s2032_generator_determines_pilotObject» — the actual-data strips agree on
     the associated pilot object.
6. **The exact first missing, proved** (section 6):
   * the actual O^× carrier cannot host the generator: every element has
     realified value 0 (`localOFieldStrip_degree_eq_one»), hence no choice of
     generator field on the O^× carrier has the q_v value
     (`oUnits_cannot_realise_qv», `oUnitsPilotedStrip_not_actualQV»).  The
     extension of the carrier from O^× to O^◃ is therefore necessary, not
     cosmetic;
   * the actual local O^◃ strip is **not** R6-proper against the reduced anchor
     (`not_r6Proper_localOFieldIntegralStrip»): R6 proper forces trivial times-mu
     fibers (S1968), but O^◃ has the nontrivial 2-torsion element -1
     (`localOFieldNegOneCanonical_*») while the reduced anchor's value monoid
     Multiplicative {x ≤ 0} has only the trivial 2-torsion element
     (`sourceHaarActualValueMonoid_mul_self_eq_one»).  Hence attaching the actual
     generator to an R6-proper *strip* requires the rebased input
     `S1978RebasedPaperInput D» (S1978), which remains the exact missing object.
   * `s2032_first_missing» packages (a), (b), and the R6-proper facts.

## Scope / honest notes

The local model is the Q_p-model of S1978 (AlgebraicClosure ℚ_[p]), not the
completion of the number field at a QPlace.  The paper's O^⊥ and the 2l-torsion
quotient are not modelled; what is modelled is the actual generator 5 ∈ O^◃ of
the local value monoid O^◃/O^×, the actual q_v element 5 ^ order_b, and the
actual norm-log realified value ρ_v (the 2l-torsion quotient does not affect the
realified value).  Target acceptance is therefore partial: the generator field is
constructed on the actual local O^◃ monoid and the realified value is proved, but
the paper's pro-object O^⊥/μ_{2l} generator and a single R6-proper strip carrying
the actual local value monoid (which requires the rebased input) are not.

## Evidence

* source file: tmp/sheaf/xif/paper/S2032R6GeneratorActual.lean, 723 lines,
  SHA256 2F8C10A92DB1C47FCF75F93BB8717C2EA8675DB22EF4A35EAC0D15BFE92D8406
* compile: lake env lean -j1 -R D:\lean -o
  .lake/build/lib/lean/tmp/sheaf/xif/paper/S2032R6GeneratorActual.olean
  tmp/sheaf/xif/paper/S2032R6GeneratorActual.lean
  EXIT=0, no errors, no warnings (log tmp/sheaf/xif/paper/_S2032build.log).
* olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S2032R6GeneratorActual.olean,
  529776 bytes, SHA256
  4EE7C24F3517E488F33D81D641CA806FD4BAB43FFFFCBEF9A40053A079EEA07C.
* axioms: all 27 probed declarations depend only on [propext, Classical.choice,
  Quot.sound]; no sorryAx.
* forbidden tokens: none (the only occurrences of the words sorry/admit are in
  docstrings).
* statement_compiles: yes.  proof_body_checked: yes.  kernel_closed: yes
  (dependency chain S1979 -> S1968 -> S1960 -> ... and S1978; not a full Project
  build).  target_accepted: partial (see Scope).

## Not run

Full Project build, target comparator acceptance, independent review, and the
`lean_auto.py» automation wrapper (direct lake compile only; a transient
Mathlib-olean read failure occurred twice under heavy parallel load and the
successful attempt is the one recorded above).
