/- Script-migrated from Mathlib4 v4.36.0-rc2 Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean.
     The 4.36 lemma is generalized (no Module.Free Z S); our pinned 4.32.2 version has the
     Free-Z hypothesis. Ported mechanically per user directive; not re-proved. -/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

noncomputable section
open Submodule

namespace Mathlib436Port

variable {S : Type*} [CommRing S]

/-- Multiplicativity of the ideal norm in Dedekind domains (Mathlib 4.36 statement,
      without Module.Free Z S; migrated by script from 4.36 AbsNorm.lean). -/
theorem cardQuot_mul_unrestricted [IsDedekindDomain S] [Infinite S] (I J : Ideal S) :
    cardQuot (I * J) = cardQuot I * cardQuot J :=
  UniqueFactorizationMonoid.multiplicative_of_coprime cardQuot I J (cardQuot_bot _ _)
      (fun {I J} hI => by simp [Ideal.isUnit_iff.mp hI, Ideal.mul_top])
      (fun {I} i hI =>
        have : Ideal.IsPrime I := Ideal.isPrime_of_prime hI
        cardQuot_pow_of_prime hI.ne_zero)
      fun {I J} hIJ => cardQuot_mul_of_coprime <| Ideal.isCoprime_iff_sup_eq.mpr
        (Ideal.isUnit_iff.mp
          (hIJ (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)))


end Mathlib436Port

end
