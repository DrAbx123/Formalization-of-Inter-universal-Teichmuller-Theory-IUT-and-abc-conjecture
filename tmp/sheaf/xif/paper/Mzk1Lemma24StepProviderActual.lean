import Mathlib
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24StepProviderActual

abbrev Qbar : Type := AlgebraicClosure ℚ

/-- **(S1a) Degree drop at critical points, PROVED** (first half of paper [Mzk1]
Lemma 2.4 lines 195-199): if x is a root of the derivative of f0 = minpoly(alpha0)
(degree d0 >= 1), then [Q(x):Q] = natDegree(minpoly x) <= d0 - 1.  Proof: minpoly x
divides f0' (minpoly.dvd), f0' is nonzero in characteristic zero, and
natDegree f0' = d0 - 1. -/
theorem s3135_criticalPoint_degree_drop (α0 x : Qbar)
    (h0 : 0 < (minpoly ℚ α0).natDegree)
    (hx : Polynomial.aeval x (Polynomial.derivative (minpoly ℚ α0)) = 0) :
    (minpoly ℚ x).natDegree ≤ (minpoly ℚ α0).natDegree - 1 := by
  have hdvd : minpoly ℚ x ∣ Polynomial.derivative (minpoly ℚ α0) :=
    minpoly.dvd (A := ℚ) (x := x) hx
  have hne : Polynomial.derivative (minpoly ℚ α0) ≠ 0 := by
    intro h
    have hz : (minpoly ℚ α0).natDegree = 0 := (Polynomial.derivative_eq_zero).mp h
    omega
  have hle := Polynomial.natDegree_le_of_dvd hdvd hne
  simpa using hle

/-- **(S1b) Value-degree drop, named class-B** (second half of paper lines 195-199):
for alpha' = f0(x) with x critical (f0'(x) = 0), [Q(alpha'):Q] <= d0 - 1.  Route:
f0(x) lies in Q(x) and Q(alpha') subset Q(x); the tower identity
[Q(x):Q] = [Q(x):Q(alpha')]*[Q(alpha'):Q] gives natDegree(minpoly alpha') <=
natDegree(minpoly x) <= d0 - 1. -/
def ValueDegreeDropStatement : Prop :=
  ∀ (α0 x : Qbar), 1 ≤ (minpoly ℚ α0).natDegree →
    Polynomial.aeval x (Polynomial.derivative (minpoly ℚ α0)) = 0 →
      (minpoly ℚ (Polynomial.aeval x (minpoly ℚ α0))).natDegree ≤
        (minpoly ℚ α0).natDegree - 1

/-- **(S1) Field-degree drop at critical points** (paper [Mzk1] Lemma 2.4 lines
195-199): the full statement; (S1a) proved, (S1b) named via ValueDegreeDropStatement. -/
def FieldDegreeDropStatement : Prop :=
  ∀ (d0 : Nat) (α0 x : Qbar),
    1 ≤ d0 →
    (minpoly ℚ α0).natDegree = d0 →
      Polynomial.aeval x (Polynomial.derivative (minpoly ℚ α0)) = 0 →
        (minpoly ℚ (Polynomial.aeval x (minpoly ℚ α0))).natDegree ≤ d0 - 1

/-- Status: (S1a) degree drop at critical points PROVED; (S1b) value-degree drop
named class-B with exact route; (S2) point-level measure decrease for S' = f0(S ∪ S0)
via MeasureActual monotonicity + Proof2 nested measure; (S3) transport composition via
P1Morphism.comp + comp_preservesSet/avoidsPoint/unramifiedOver + normalization transfer
bundle.  Consumed by Mzk1Lemma24AssemblyActual.mzk1Lemma24_assembly.  No closure claim;
registry frozen 14041. -/
def Mzk1Lemma24StepProviderStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.step-provider"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 195-206"
    status := Audit.VerificationStatus.interface
    note := "DECOMPOSITION of the single remaining 2.4 residue: (S1a) s3135_criticalPoint_degree_drop PROVED (minpoly.dvd + natDegree_le_of_dvd + natDegree_derivative; char-0 nonzero derivative); (S1b) ValueDegreeDropStatement named class-B (value f0(x) degree via Q(f0(x)) subset Q(x) and tower finrank); (S2) point-level measure decrease of S' = f0(S union S0) using S1 + MeasureActual monotonicity + Proof2 nested measure; (S3) transport composition via P1Morphism.comp + comp_preservesSet/avoidsPoint/unramifiedOver + normalization/affine transfer bundle. All other 2.4 components PROVED (G/F/D/M interface evidence, L2.3 numeric normalization + transfer, rational base case for Q, nested assembly skeleton mzk1Lemma24_assembly). No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.assembly", "MZK1.lemma24.f0-coefficient-bound" ]
    sorryItems :=
      [ "(S1b) ValueDegreeDropStatement (class-B named)",
        "(S2) point-level measure decrease instantiation",
        "(S3) transport composition wiring to assembly step record" ] }

#check s3135_criticalPoint_degree_drop
#check ValueDegreeDropStatement
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24StepProviderActual
end