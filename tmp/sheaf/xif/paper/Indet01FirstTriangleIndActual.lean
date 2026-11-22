import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteMultiradial
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind3UpperSemiConstruction
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Indet01: first-triangle (Ind1),(Ind2),(Ind3) indeterminacy structure (statement layer)

Paper source: IUT III, Theorem 3.11, (Ind1)/(Ind2)/(Ind3) — corpus lines 653-679;
MHYY "Formalization of IUT (2026-04)" §4 (first triangle = BPS -> multiradial
representation, constructed up to (Ind1,2,3)).

Reuse (no re-proof): the production generic multiradial kernel
(MultiradialOutputKernel.Core, with Ind1Step/Ind2Step/Ind3Step and the generated
quotient) and its proved finite instance SourceFiniteMultiradial.core/profile:
* (Ind1): automorphisms of the procession of D-prime-strips / permutation
  automorphisms of the label sets S±_{j+1} — ProcessionChoice.ind1Act
  (corpus 655-660);
* (Ind2): the non-(Ind1) Z^x / units action on local copies of O^x mu —
  ProcessionChoice.ind2Act (corpus 661-667);
* (Ind3): the one-sided upper-semi lift — ProcessionChoice.ind3Lift, with the
  proved upper-semi law Ind3UpperSemi.outputImageFamily_upper (corpus 668-672).

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Indet01FirstTriangleIndActual

open LeanFormal.IUT
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.MultiradialKernel.Core
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.SourceFiniteMultiradial
open LeanFormal.IUT.Ind3UpperSemi

universe u

/-- (Ind1) action on the first triangle (corpus IUT III 655-660). -/
def firstTriangleInd1 (l : PrimeGeFive) (g : finiteLabel l)
    (c : ProcessionChoice l) : ProcessionChoice l :=
  ProcessionChoice.ind1Act g c

/-- (Ind2) action on the first triangle (corpus IUT III 661-667). -/
def firstTriangleInd2 (l : PrimeGeFive) (g : finiteLabel l)
    (c : ProcessionChoice l) : ProcessionChoice l :=
  ProcessionChoice.ind2Act g c

/-- (Ind3) one-sided lift on the first triangle (corpus IUT III 668-672). -/
def firstTriangleInd3 (l : PrimeGeFive) (n : Nat)
    (c : ProcessionChoice l) : ProcessionChoice l :=
  ProcessionChoice.ind3Lift n c

/-- (Ind1) leaves the vertical level invariant. -/
theorem firstTriangleInd1_level (l : PrimeGeFive) (g : finiteLabel l)
    (c : ProcessionChoice l) :
    (core l).level (firstTriangleInd1 l g c) = (core l).level c :=
  (core l).ind1_level g c

/-- (Ind2) leaves the vertical level invariant. -/
theorem firstTriangleInd2_level (l : PrimeGeFive) (g : finiteLabel l)
    (c : ProcessionChoice l) :
    (core l).level (firstTriangleInd2 l g c) = (core l).level c :=
  (core l).ind2_level g c

/-- (Ind3) is one-sided: the lift only raises the vertical level. -/
theorem firstTriangleInd3_level (l : PrimeGeFive) (n : Nat)
    (c : ProcessionChoice l) :
    (core l).level c ≤ (core l).level (firstTriangleInd3 l n c) :=
  (core l).ind3_level n c

/-- (Ind3) upper-semi law for the first-triangle image family (reused proved law). -/
theorem firstTriangleInd3_upperSemi (l : PrimeGeFive) (c : ProcessionChoice l) :
    IsUpperSemi (outputImageFamily l c) :=
  outputImageFamily_upper l c

/-- The first-triangle indeterminacy bundle: the three actions with their laws. -/
structure FirstTriangleIndeterminacy (l : PrimeGeFive) where
  /-- (Ind1) action -/
  ind1 : finiteLabel l → ProcessionChoice l → ProcessionChoice l
  /-- (Ind2) action -/
  ind2 : finiteLabel l → ProcessionChoice l → ProcessionChoice l
  /-- (Ind3) one-sided lift -/
  ind3 : Nat → ProcessionChoice l → ProcessionChoice l
  /-- (Ind1) preserves level -/
  ind1_level : ∀ g c, (core l).level (ind1 g c) = (core l).level c
  /-- (Ind2) preserves level -/
  ind2_level : ∀ g c, (core l).level (ind2 g c) = (core l).level c
  /-- (Ind3) raises level (one-sided) -/
  ind3_level : ∀ n c, (core l).level c ≤ (core l).level (ind3 n c)
  /-- (Ind3) upper-semi law of the image family -/
  ind3_upperSemi : ∀ c, IsUpperSemi (outputImageFamily l c)

/-- The canonical first-triangle indeterminacy structure (reused finite instance). -/
def firstTriangleIndeterminacy (l : PrimeGeFive) : FirstTriangleIndeterminacy l where
  ind1 := firstTriangleInd1 l
  ind2 := firstTriangleInd2 l
  ind3 := firstTriangleInd3 l
  ind1_level := firstTriangleInd1_level l
  ind2_level := firstTriangleInd2_level l
  ind3_level := firstTriangleInd3_level l
  ind3_upperSemi := firstTriangleInd3_upperSemi l

/-- Paper anchors (corpus lines, exact). -/
def firstTriangleIndCitations : List (String × String) :=
  [ ("IUT III 653-679", "Theorem 3.11 (Ind1)/(Ind2)/(Ind3) definitions"),
    ("IUT III 655-660", "(Ind1): automorphisms of processions of D-prime-strips / label-set permutations S±_{j+1}"),
    ("IUT III 661-667", "(Ind2): non-(Ind1) Z^x / O^x mu indeterminacies on the F×mu-prime-strips"),
    ("IUT III 668-672", "(Ind3): upper semi-compatibility of the log-Kummer correspondences"),
    ("MHYY 2026-04 §4 (472-501)", "first triangle: BPS -> multiradial representation, constructed up to a full poly-isomorphism") ]

end LeanFormal.IUT.XiFPaper.Indet01FirstTriangleIndActual

end
