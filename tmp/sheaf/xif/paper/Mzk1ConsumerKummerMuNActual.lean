import LeanFormal/IUT/IUTIII/Theorem311/SourceK1K2KummerPrimeLift
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceLogShellMuNQuotientCarrier

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ConsumerKummerMuNActual — A476 real consumer theorems (Kummer lift / muN quotient)

New conclusions combining existing donor theorems:

* K1/K2 Kummer prime lift (\`SourceK1K2KummerPrimeLift.lean:94/105/118/131\`):
  - \`labelledKummerIso_nonempty_chain\`: general conditional iso theorem +
    prime-exponent irreducibility -> unconditional existence (chain);
  - \`kummer_lift_injective_and_iso\`: injectivity + nonempty iso jointly.
* muN quotient (\`SourceLogShellMuNQuotientCarrier.lean:75/80/96/106\`):
  - \`muN_quotient_structure\`: kernel = torsion and surjectivity jointly;
  - \`muN_pow_end_chain\`: power map commutes with the quotient map (reverse
    orientation of the computation law);
  - \`weightNLog_pow_consumer\`: normalized weight-N log of an N-th power.

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ConsumerKummerMuNActual

open LeanFormal.IUT
open LeanFormal.IUT.K1K2Realization

/-- **Labelled Kummer iso chain consumer**: from prime-exponent irreducibility
plus the general conditional iso theorem. -/
theorem labelledKummerIso_nonempty_chain (p n : Nat) [Fact (Nat.Prime p)] (hn : n.Prime) :
    Nonempty (LabelledKummerIso (localKummerPolynomialFor p n hn.pos).Adjoined
      (Set.range ((localKummerRootRealizationFor p n hn.pos).lift
        (localKummerPolynomialFor p n hn.pos) (AlgebraicClosure ℚ_[p])))) :=
  labelledKummerIso_nonempty_of_irreducible_localKummerPolynomial p n hn.pos
    (localKummerPolynomial_irreducible_of_prime_exponent p n hn)

/-- **Kummer injectivity + iso package consumer**. -/
theorem kummer_lift_injective_and_iso (p n : Nat) [Fact (Nat.Prime p)] (hn : n.Prime) :
    Function.Injective
        ((localKummerRootRealizationFor p n hn.pos).lift
          (localKummerPolynomialFor p n hn.pos) (AlgebraicClosure ℚ_[p])) ∧
      Nonempty (LabelledKummerIso (localKummerPolynomialFor p n hn.pos).Adjoined
        (Set.range ((localKummerRootRealizationFor p n hn.pos).lift
          (localKummerPolynomialFor p n hn.pos) (AlgebraicClosure ℚ_[p])))) :=
  ⟨localKummerLift_injective_of_prime_exponent p n hn,
   labelledKummerIso_nonempty_chain p n hn⟩

/-- **muN quotient structure consumer**: kernel and surjectivity jointly. -/
theorem muN_quotient_structure (D : SourceLogShellDatum) :
    MonoidHom.ker D.muNQuotientMap = CommGroup.torsion D.Units ∧
      Function.Surjective D.muNQuotientMap :=
  ⟨D.muNQuotientMap_ker, D.muNQuotientMap_surjective⟩

/-- **muN power-end chain consumer**: the quotient map of an N-th power equals
the descended power endomorphism (reverse orientation of the computation law). -/
theorem muN_pow_end_chain (D : SourceLogShellDatum) (N : Nat) (u : D.Units) :
    D.muNQuotientMap (u ^ N) = D.muNPowEnd N (D.muNQuotientMap u) :=
  (D.muNPowEnd_quotientMap N u).symm

/-- **Weight-N log consumer**: the normalized weight-N log of an N-th power is
the log of the element. -/
theorem weightNLog_pow_consumer (D : SourceLogShellDatum) (N : Nat) (hN : N ≠ 0)
    (u : D.Units) :
    D.weightNLog N (u ^ N) = (D.logMap u).toAdd :=
  D.weightNLog_pow N hN u

#check kummer_lift_injective_and_iso
#check muN_quotient_structure

end LeanFormal.IUT.XiFPaper.Mzk1ConsumerKummerMuNActual
end