/- Route 3.3 (de-conditionalization): the three different notions are kept as separate actual
objects.  (1) absolute differential Omega_{Y/k}; (2) relative differential Omega_{Y/P^1} as the
cokernel of d(lambda), lambda = x^n; (3) arithmetic different as the relative different ideal.
The old RelativeDifferentialInterface (NO INHABITANT) is now actually inhabited. -/
import tmp.sheaf.xif.paper.Mzk1G1OmegaLineBundleDataActual
import tmp.sheaf.xif.paper.Mzk1G1RelativeDifferentPlaceSumActual
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ThreeDifferentActualActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleDataActual

universe u

/-- (1) The absolute differential Omega_{Y/k} on the affine chart U0. -/
abbrev absoluteDifferential0 (n : Nat) : Type := KaehlerDifferential ℚ (B n)

/-- (2) The relative differential Omega_{Y/P^1} on U0: the cokernel of d(lambda), where the
pullback of the P^1 coordinate is lambda = x^n = u0^n. -/
abbrev relativeDifferential0 (n : Nat) : Type :=
  KaehlerDifferential ℚ (O0 n) ⧸
    Submodule.span (O0 n) ({KaehlerDifferential.D ℚ (O0 n) (u0 n ^ n)} :
      Set (KaehlerDifferential ℚ (O0 n)))

instance relativeDifferential0_addCommGroup (n : Nat) : AddCommGroup (relativeDifferential0 n) :=
  inferInstance

instance relativeDifferential0_module (n : Nat) : Module (O0 n) (relativeDifferential0 n) :=
  inferInstance

/-- The previously NO-INHABITANT relative-differential interface is now inhabited by the
actual cokernel of d(lambda). -/
def relativeDifferentialInterface (n : Nat) : RelativeDifferentialInterface n where
  carrier := relativeDifferential0 n
  addCommGroup := relativeDifferential0_addCommGroup n
  module := relativeDifferential0_module n

theorem relativeDifferentialInterface_nonempty (n : Nat) :
    Nonempty (RelativeDifferentialInterface n) :=
  ⟨relativeDifferentialInterface n⟩

/-- (3) The arithmetic different actual object: the relative different ideal. -/
structure ArithmeticDifferentActual (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L] where
  different : Ideal (𝓞 L)

/-- The arithmetic different is instantiated by the relative different ideal. -/
def arithmeticDifferent (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [Module.Finite (𝓞 K) (𝓞 L)] : ArithmeticDifferentActual K L where
  different := differentIdeal (𝓞 K) (𝓞 L)

theorem arithmeticDifferentActual_nonempty (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    [Module.Finite (𝓞 K) (𝓞 L)] : Nonempty (ArithmeticDifferentActual K L) :=
  ⟨arithmeticDifferent K L⟩

#print axioms relativeDifferentialInterface_nonempty
#print axioms arithmeticDifferentActual_nonempty
end LeanFormal.IUT.XiFPaper.Mzk1G1ThreeDifferentActualActual
