import tmp.sheaf.xif.paper.S3133RealifiedQPilotDivisorActual
import tmp.sheaf.n8.closure.NativeInput

/-!
# Real-indexed degree-faithful value-group generator (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: abc task-33(a) value-group degree
splitting; mainline model map degree readouts; lattice R1 q-side log-volume.

Source: IUT II, Example 1.8, (ix) (value-group degree); [AbsTopIII],
Proposition 5.8, (ii); IUT III, Remark 3.9.4; IUT III, Proposition 3.9, (i),
p. 115 (realified log-volume compatibility).

On the actual realified global divisor group of C^boxplus_mod
(GlobalRealifiedFrobenioidActual) this file constructs, for every actual global
prime place v, the actual REAL-indexed generator family

  r : Real |-> [v]^r            (divisor with real coefficient r at v)

and proves the exact degree readout

  globalDegree ([v]^r) = ofAdd (r * globalPrimeWeight v),

its monoid-hom form Multiplicative Real ->* GlobalDivisorMonoid, the Int-indexed
q^Z specialisation, and injectivity (degree faithfulness) when the arithmetic
weight of v is nonzero.  These are actual objects on the actual carrier; no
arbitrary carrier or action is introduced.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotDivisorActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The actual realified prime power [v]^r with real coefficient r at the
global place v (an element of the actual realified divisor group). -/
noncomputable def globalRealifiedPrimePower
    (v : GlobalPrimeIndex (X := X)) (r : Real) :
    GlobalDivisorMonoid (X := X) :=
  Multiplicative.ofAdd (Finsupp.single v r)

/-- The actual realified degree readout of [v]^r: r times the arithmetic weight
of v. -/
theorem globalDegree_realifiedPrimePower
    (v : GlobalPrimeIndex (X := X)) (r : Real) :
    globalDegree (X := X) (globalRealifiedPrimePower X v r) =
      Multiplicative.ofAdd (r * globalPrimeWeight (X := X) v) := by
  unfold globalRealifiedPrimePower
  change Multiplicative.ofAdd (globalDegreeFun (X := X) (Finsupp.single v r)) =
    Multiplicative.ofAdd (r * globalPrimeWeight (X := X) v)
  congr 1
  unfold globalDegreeFun
  simp

/-- The actual Real-indexed generator homomorphism Multiplicative Real ->*
realified divisor monoid at the global place v. -/
noncomputable def globalRealifiedPrimePowerHom
    (v : GlobalPrimeIndex (X := X)) :
    Multiplicative Real →* GlobalDivisorMonoid (X := X) where
  toFun r := globalRealifiedPrimePower X v r.toAdd
  map_one' := by
    unfold globalRealifiedPrimePower
    simp
  map_mul' r s := by
    unfold globalRealifiedPrimePower
    simp [toAdd_mul, Finsupp.single_add]

/-- The composed degree readout of the Real-indexed generator: r |-> r * weight v
as a multiplicative real number. -/
theorem globalDegree_comp_primePowerHom
    (v : GlobalPrimeIndex (X := X)) (r : Multiplicative Real) :
    globalDegree (X := X) (globalRealifiedPrimePowerHom X v r) =
      Multiplicative.ofAdd (r.toAdd * globalPrimeWeight (X := X) v) :=
  globalDegree_realifiedPrimePower X v r.toAdd

/-- The Int-indexed q^Z readout: the z-th power of the actual prime divisor has
degree z times the arithmetic weight. -/
theorem globalDegree_primeDivisor_zpow
    (v : GlobalPrimeIndex (X := X)) (z : Int) :
    globalDegree (X := X) (globalPrimeDivisor (X := X) v ^ z) =
      Multiplicative.ofAdd (z • globalPrimeWeight (X := X) v) := by
  rw [map_zpow, globalDegree_primeDivisor]
  exact ofAdd_zsmul z (globalPrimeWeight (X := X) v)

/-- Degree faithfulness on the q^Z generator: for nonzero arithmetic weight the
Real-indexed generator has trivial degree kernel. -/
theorem globalRealifiedPrimePowerHom_degree_faithful
    (v : GlobalPrimeIndex (X := X))
    (hweight : globalPrimeWeight (X := X) v ≠ 0)
    (r s : Multiplicative Real)
    (h : globalDegree (X := X) (globalRealifiedPrimePowerHom X v r) =
      globalDegree (X := X) (globalRealifiedPrimePowerHom X v s)) :
    r = s := by
  rw [globalDegree_comp_primePowerHom, globalDegree_comp_primePowerHom] at h
  have hmul : r.toAdd * globalPrimeWeight (X := X) v =
      s.toAdd * globalPrimeWeight (X := X) v := by
    exact Multiplicative.ofAdd.injective h
  have hsub : (r.toAdd - s.toAdd) * globalPrimeWeight (X := X) v = 0 := by
    rw [sub_mul, hmul, sub_self]
  have hzero : r.toAdd - s.toAdd = 0 := by
    rcases mul_eq_zero.mp hsub with h0 | h0
    · exact h0
    · exact absurd h0 hweight
  have : r.toAdd = s.toAdd := sub_eq_zero.mp hzero
  exact Multiplicative.toAdd.injective this

end LeanFormal.IUT.XiFPaper.S3133ValueGroupDegreeActual
