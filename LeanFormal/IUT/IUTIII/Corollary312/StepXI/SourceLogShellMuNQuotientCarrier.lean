import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# S2-W-1 reduced carrier: the torsion quotient of the log-shell unit layer and the
weight-N normalized log

The relocated card S2-W-1 (section 19.3 of
`logs/coordination/outsider-survey-transport-20261016.md`) concerns the object
`Ψ^gp/Ψ^{μN}` [or `Ψ^×/Ψ^{μN}`] of IUT III, Remark 1.2.1, (i) (text l.2128-2160):
the metric of `Ψ^gp` is descended, but the quotient object is regarded as equipped
with a "weight N" — which has the effect of ensuring that the log-volume of
`Ψ^×/Ψ^{μN}` is equal to that of `Ψ^×`, so that working with the quotient does not
affect log-volume computations.

This module provides the reduced carrier and the reduced weight-N law on the
log-shell datum of `SourceLogShellCarrier.lean` (whose `Units` field is the
reduced `Ψ×_{†F_v}`):

* `SourceLogShellDatum.muNQuotient` — the quotient carrier `Ψ^×/μ`, realized by
  the repository-wide times-mu quotient (quotient by the full torsion subgroup);
* `SourceLogShellDatum.muNQuotientMap` — the quotient map, with kernel and
  surjectivity;
* `SourceLogShellDatum.muNPowEnd` — the descended `N`-th power endomorphism of
  the quotient (torsion is closed under powers), with the computation law;
* `SourceLogShellDatum.weightNLog` — the weight-`N` normalized log coordinate
  `(log u)/N`, and `weightNLog_pow` — the reduced weight-N convention: under the
  normalized log the `N`-th power is invisible,
  `weightNLog D N (u ^ N) = logMap u`.

## Reductions (labeled; not substituting the paper)

1. The quotient is by the full torsion subgroup of the reduced unit carrier, not
   by the `μN`-level filtration: the reduced carrier does not carry the
   `μN`-filtration (the discrepancy `μ(K)/μN` is not modeled).
2. The metric descent of Remark 1.2.1, (i) is not formalized (no metrics on the
   reduced `K`-valued carrier).
3. The log-volume equality "of the quotient = of `Ψ^×`" is realized at the
   log-coordinate level by the normalization law `weightNLog_pow`; the faithful
   log-volume landing (Proposition 3.9 / (Ob3-1), text l.7936-7959) remains a
   separate consumption line and is NOT asserted here.
4. The archimedean case and all topology/compactness statements are not treated
   (as in the carrier module).

## Consumer

The log-volume consumption line / the "second wall" normalization face: the
consumer can pass to the quotient, act by `muNPowEnd`, and normalize logs by
`weightNLog` without changing log values (`weightNLog_pow`).
-/

namespace LeanFormal.IUT

universe u

noncomputable section

namespace SourceLogShellDatum

/-- The reduced `μ`-quotient carrier of the log-shell unit layer: `Ψ^×/μ`,
realized as the times-mu quotient (quotient by the full torsion subgroup) of the
reduced unit carrier `D.Units`. -/
abbrev muNQuotient (D : SourceLogShellDatum) : Type u :=
  TimesMuQuotient D.Units

/-- The quotient map `Ψ^× → Ψ^×/μ` of the reduced carrier. -/
def muNQuotientMap (D : SourceLogShellDatum) : D.Units →* D.muNQuotient :=
  TimesMuQuotient.quotientMap

/-- The kernel of the reduced quotient map is the torsion subgroup of the unit
carrier. -/
theorem muNQuotientMap_ker (D : SourceLogShellDatum) :
    MonoidHom.ker D.muNQuotientMap = CommGroup.torsion D.Units :=
  TimesMuQuotient.quotientMap_ker

/-- The reduced quotient map is surjective. -/
theorem muNQuotientMap_surjective (D : SourceLogShellDatum) :
    Function.Surjective D.muNQuotientMap :=
  TimesMuQuotient.quotientMap_surjective

/-- The descended `N`-th power endomorphism of the reduced quotient: the power
map is a homomorphism of the commutative unit carrier, and torsion is closed
under powers, so it descends to `Ψ^×/μ`. -/
def muNPowEnd (D : SourceLogShellDatum) (N : ℕ) :
    D.muNQuotient →* D.muNQuotient :=
  QuotientGroup.map (CommGroup.torsion D.Units) (CommGroup.torsion D.Units)
    (powMonoidHom N : D.Units →* D.Units)
    (CommGroup.le_comap_torsion (powMonoidHom N : D.Units →* D.Units))

/-- Computation law of the descended power endomorphism on quotient classes. -/
@[simp] theorem muNPowEnd_quotientMap (D : SourceLogShellDatum) (N : ℕ)
    (u : D.Units) :
    D.muNPowEnd N (D.muNQuotientMap u) = D.muNQuotientMap (u ^ N) :=
  rfl

/-- The weight-`N` normalized log coordinate: divide the log coordinate by `N`
(the reduced form of the "weight N" convention of Remark 1.2.1, (i)). -/
def weightNLog (D : SourceLogShellDatum) (N : ℕ) (u : D.Units) : D.K :=
  (N : D.K)⁻¹ * (D.logMap u).toAdd

/-- The reduced weight-`N` convention: under the normalized log, the `N`-th
power is invisible — the normalized log of `u ^ N` is the log of `u`. -/
theorem weightNLog_pow (D : SourceLogShellDatum) (N : ℕ) (hN : N ≠ 0)
    (u : D.Units) :
    D.weightNLog N (u ^ N) = (D.logMap u).toAdd := by
  unfold weightNLog
  rw [D.logMap_pow_val u N, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN), one_mul]

end SourceLogShellDatum

end

namespace Audit

/-- S2-W-1 reduced carrier: the torsion quotient of the reduced log-shell unit
layer, the descended power endomorphism, and the weight-N normalized log law. -/
def sourceLogShellWeightNQuotient : Obligation :=
  { id := "IUT-III.source-log-shell-weightN-quotient"
    source :=
      "IUT III, Remark 1.2.1, (i) (text l.2128-2160: Ψ^gp/Ψ^{μN} and the " ++
        "weight-N convention); IUT III, Definition 1.1, (i) (log-shell carrier)"
    status := VerificationStatus.interface
    note :=
      "Reduced carrier for the relocated card S2-W-1. Provided: the quotient " ++
        "carrier muNQuotient (times-mu quotient of the reduced unit carrier " ++
        "Psi^x), its quotient map with kernel (the torsion subgroup) and " ++
        "surjectivity, the descended N-th power endomorphism muNPowEnd with " ++
        "computation law, the log-scaling law (via the carrier logMap_pow_val), and the " ++
        "weight-N normalized log weightNLog with the invisibility law " ++
        "weightNLog_pow. Reductions (labeled): the quotient is by the full " ++
        "torsion subgroup, not by the muN-level filtration (mu(K)/muN not " ++
        "modeled); the metric descent of Rem 1.2.1, (i) is not formalized; the " ++
        "log-volume equality of Psi^x/muN and Psi^x is realized at the " ++
        "log-coordinate level by weightNLog_pow, not as a measure-theoretic " ++
        "identity; the log-volume landing (Proposition 3.9 / (Ob3-1)) remains a " ++
        "separate consumption line. The archimedean case is not treated."
    dependsOn :=
      [ "IUT-II.source-log-shell-carrier",
        "IUT-II.times-mu-torsion-quotient" ] }

end Audit

end LeanFormal.IUT
