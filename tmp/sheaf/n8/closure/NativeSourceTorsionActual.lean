import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Native SourceTorsionClause from clause (c), via the existing D5 constructor

This file builds the actual SourceTorsionClause of
SourceDefinition31Boundary.lean from the native clause (c) SourceClauseC of
SourceDefinition31Quantifiers.lean, reusing the existing D5 bridge
D5TorsionSupply.toTorsionClause of SourceDefinition31D4D9Supply.lean.

Actual data used:

* torsion carrier: Multiplicative (A.curve.LTorsion l), the actual l-torsion
  subgroup of the source curve;
* D5 datum: TorsionCarrierReduction.SourceTorsionDatum.ofSourceClauseC D,
  the actual rank-two torsion basis, literal SL2 containment, and kernel-field
  identification from the native clause (c);
* representation, range group, range-restricted surjective map, and the
  imageContainsSL2 proof: supplied by D5TorsionSupply.toTorsionClause from the
  actual D5 datum.

Exact missing native fields, kept as explicit hypotheses:

1. torsionLabel : Multiplicative (A.curve.LTorsion l) -> Fin 6.
   SourceClauseC does not construct the six-slot labelling; the labelled
   six-slot carrier is a separate source-side object.
2. sixTorsionIndependent : Prop and its proof.
   SourceClauseC supplies torsion23_rational, which is not the same as
   six-torsion independence.
3. lTorsionCompatible : Prop and its proof.
   SourceClauseC does not state the q-parameter/l-torsion compatibility.

No arbitrary type, placeholder proposition, trivial unit, fake proof, or uninterpreted declaration is used.
-/

noncomputable section

namespace LeanFormal.IUT
namespace InitialThetaSource
namespace NativeSourceTorsion

open Definition31D4D9Supply

universe u

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}

/-- The actual native torsion carrier: the l-torsion of the source curve,
made multiplicative for the Group-valued SourceTorsionClause slot. -/
abbrev nativeTorsionCarrier : Type u :=
  rootsOfUnity 6 (AlgebraicClosure A.F)

/-- The actual clause-(c) D5 datum, obtained by the existing recognition
constructor SourceTorsionDatum.ofSourceClauseC. -/
noncomputable def nativeTorsionDatum
    (D : SourceClauseC A S C B) :
    TorsionCarrierReduction.SourceTorsionDatum l A :=
  TorsionCarrierReduction.SourceTorsionDatum.ofSourceClauseC D

/-- The explicit D5 supply assembled from the native clause (c) and the three
missing source condition fields. -/
noncomputable def nativeD5TorsionSupply
    (D : SourceClauseC A S C B)
    (torsionLabel : nativeTorsionCarrier (A := A) (l := l) → Fin 6)
    (sixTorsionIndependent : Prop)
    (sixTorsionIndependent_proved : sixTorsionIndependent)
    (lTorsionCompatible : Prop)
    (lTorsionCompatible_proved : lTorsionCompatible) :
    D5TorsionSupply l A where
  datum := nativeTorsionDatum D
  torsionCarrier := nativeTorsionCarrier (A := A) (l := l)
  torsionCarrierLaw := inferInstance
  torsionLabel := torsionLabel
  torsionNonempty := ⟨1⟩
  sixTorsionIndependent := sixTorsionIndependent
  sixTorsionIndependent_proved := sixTorsionIndependent_proved
  lTorsionCompatible := lTorsionCompatible
  lTorsionCompatible_proved := lTorsionCompatible_proved

/-- The native SourceTorsionClause, constructed by reusing the existing D5
bridge D5TorsionSupply.toTorsionClause. -/
noncomputable def nativeSourceTorsionClause
    (D : SourceClauseC A S C B)
    (torsionLabel : nativeTorsionCarrier (A := A) (l := l) → Fin 6)
    (sixTorsionIndependent : Prop)
    (sixTorsionIndependent_proved : sixTorsionIndependent)
    (lTorsionCompatible : Prop)
    (lTorsionCompatible_proved : lTorsionCompatible) :
    Theorem311Source.SourceTorsionClause l :=
  (nativeD5TorsionSupply D torsionLabel sixTorsionIndependent
    sixTorsionIndependent_proved lTorsionCompatible
    lTorsionCompatible_proved).toTorsionClause

/-- Recognition: the constructed torsion clause has the actual l-torsion
carrier. -/
theorem nativeSourceTorsionClause_torsionCarrier
    (D : SourceClauseC A S C B)
    (torsionLabel : nativeTorsionCarrier (A := A) (l := l) → Fin 6)
    (sixTorsionIndependent : Prop)
    (sixTorsionIndependent_proved : sixTorsionIndependent)
    (lTorsionCompatible : Prop)
    (lTorsionCompatible_proved : lTorsionCompatible) :
    (nativeSourceTorsionClause D torsionLabel sixTorsionIndependent
      sixTorsionIndependent_proved lTorsionCompatible
      lTorsionCompatible_proved).torsionCarrier =
      nativeTorsionCarrier (A := A) (l := l) := rfl

/-- Recognition: the clause-(c) torsion23_rational remains available and is
not converted into the missing six-torsion independence hypothesis. -/
theorem native_torsion23_rational
    (D : SourceClauseC A S C B) :
    PuncturedEllipticCurve.Torsion23Rational A.curve :=
  D.torsion23_rational

/-- The native clause's actual l-torsion basis. -/
noncomputable def native_torsion_basis
    (D : SourceClauseC A S C B) :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l :=
  D.torsion_basis

/-- The exact remaining gap ledger for the native construction. -/
structure NativeSourceTorsionGaps
    (D : SourceClauseC A S C B) where
  torsionLabel : nativeTorsionCarrier (A := A) (l := l) → Fin 6
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent
  lTorsionCompatible : Prop
  lTorsionCompatible_proved : lTorsionCompatible

/-- A gap package yields the native torsion clause via the existing D5
constructor. -/
noncomputable def NativeSourceTorsionGaps.toSourceTorsionClause
    {D : SourceClauseC A S C B} (G : NativeSourceTorsionGaps D) :
    Theorem311Source.SourceTorsionClause l :=
  nativeSourceTorsionClause D G.torsionLabel G.sixTorsionIndependent
    G.sixTorsionIndependent_proved G.lTorsionCompatible
    G.lTorsionCompatible_proved

end NativeSourceTorsion
end InitialThetaSource
end LeanFormal.IUT

end
