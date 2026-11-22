import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic

/-! # A816 paper box constant audit

Primary source: IUT IV, Theorem 1.10, Step (v) (local corpus
`papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt`,
L1736–L1783).  The exact procession-normalized upper bound is

  `(l+5)/4 * D - (l+1)/24 * Q + S + (l+5) * T`

with `D = log d^K`, `Q = log q`, `S = log s^Q`, `T = l*_mod * log s^<=`,
and then

  `... <= (l+1)/4 * ((1+4/l)*D - Q/6 + (4/l)*S + (20/3)*T)`.

Here `S` and `T` are NOT absolute constants: `T = log(e*_mod*l) * log s^<=`
grows with `l` (and with the bounded moduli data).  The project shape
`V <= (1/4)*l*(log d + log f) + C0` drops the `- (l+1)/24*Q` term, replaces
`D = log d^K` by `log d + log f`, and treats the `S,(l+5)T` terms as an
absolute `C0`.  Hence it is not literally the paper Step-V bound.

Arithmetic core: with `c(l) = (l+1)/24 - 1/(2l) = (l+4)(l-3)/(24l)`,
`(l+5)/(4c(l)) = 6*l*(l+5)/((l+4)(l-3)) = 6*(1 + 4*(l+3)/((l+4)(l-3)))`.
Thus the finite-l Szpiro constant is `T(l) = 6*l*(l+5)/((l+4)(l-3)) > 6`
for `l >= 5`; using constant `6` at finite `l` is slightly STRONGER than the
paper, while using `1/4*l*logdf` with a uniform `C0` is a different shape.

The Step-V exceptional sum is bounded by the green theorem
`exceptionaSum_le_r4`/`processionAverage_le`, not by an absolute constant. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1BoxConstantAuditActual

open LeanFormal.IUT.IUTIV.StepVProcessionAverage

/-- The SSIneq coefficient `c(l)`. -/
noncomputable def cBox (l : Real) : Real := (l + 1) / 24 - 1 / (2 * l)

/-- Arithmetic identity: the Szpiro constant from the paper box ratio. -/
theorem cBox_eq {l : Real} (hl0 : l ≠ 0) :
    cBox l = (l + 4) * (l - 3) / (24 * l) := by
  unfold cBox
  field_simp [hl0]
  ring

/-- The same ratio in the `T(l)` form. -/
theorem boxRatio_eq_T {l : Real} (hl : 3 < l) :
    (l + 5) / (4 * cBox l) = 6 * l * (l + 5) / ((l + 4) * (l - 3)) := by
  have hl0 : l ≠ 0 := by linarith
  have h4 : l + 4 ≠ 0 := by linarith
  have h3 : l - 3 ≠ 0 := by linarith
  rw [cBox_eq hl0]
  field_simp [hl0, h4, h3]
  ring

/-- Arithmetic identity: `(l+5)/(4c(l)) = 6*(1+eps(l))` with
`eps(l) = 4(l+3)/((l+4)(l-3))`. -/
theorem boxRatio_eq_eps {l : Real} (hl : 3 < l) :
    (l + 5) / (4 * cBox l) =
      6 * (1 + 4 * (l + 3) / ((l + 4) * (l - 3))) := by
  have hl0 : l ≠ 0 := by linarith
  have h4 : l + 4 ≠ 0 := by linarith
  have h3 : l - 3 ≠ 0 := by linarith
  rw [cBox_eq hl0]
  field_simp [hl0, h4, h3]
  ring

/-- Step-V exact procession bound (re-export of the green paper Step-V theorem). -/
theorem paper_procession_le (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    (1 / (n : Real)) *
        (∑ j ∈ Finset.Icc 1 n, collectionBound (2 * (n : Real) + 1) D Q S T j) ≤
      ((2 * (n : Real) + 1) + 1) / 4 *
        ((1 + 4 / (2 * (n : Real) + 1)) * D - Q / 6 +
          4 / (2 * (n : Real) + 1) * S + 20 / 3 * T) :=
  processionAverage_le n hn D Q S T hD hS hT

/-- Step-V exceptional-term bound (re-export of the green (R4) bound). -/
theorem paper_exception_le {α : Type*} (I Istar : Finset α) (hsub : Istar ⊆ I)
    (e : α → Real) (p el : Real) (hel : 1 ≤ el)
    (hR4 : forall i, i ∈ Istar → p ≤ el ∧ Real.log (e i) ≤ -3 + 4 * Real.log el) :
    (∑ i ∈ Istar, (3 + Real.log (e i))) ≤
      4 * (I.card : Real) * (if p ≤ el then Real.log el else 0) :=
  exceptionalSum_le_r4 I Istar hsub e p el hel hR4

structure BoxConstantRow where
  item : String
  paper : String
  project : String
  verdict : String

def boxConstantRows : List BoxConstantRow :=
  [ { item := "leading D coefficient", paper := "(l+5)/4 * log d^K", project := "(1/4) * l * logdf", verdict := "paper has (l+5)/4 and D=log d^K; project l/4 differs by finite-l term" },
    { item := "Q coefficient", paper := "-(l+1)/24 * log q (kept negative)", project := "absent (dropped)", verdict := "project upper-bound shape is different; dropping -Q term can be too strong/too weak depending on q" },
    { item := "exception S", paper := "log s^Q", project := "absorbed in C0", verdict := "S is not shown absolute" },
    { item := "exception T", paper := "(l+5) * l*_mod * log s^<=", project := "absorbed in C0", verdict := "T grows with l; requires (R4)/Section1 bounds" },
    { item := "finite-l Szpiro constant", paper := "T(l)=6l(l+5)/((l+4)(l-3)) > 6", project := "6", verdict := "project constant 6 at finite l is STRONGER than paper Step V" },
    { item := "epsilon conversion", paper := "(l+5)/(4c) = 6(1+eps(l))", project := "eps not explicit", verdict := "eps(l)=4(l+3)/((l+4)(l-3)) explicit" } ]

def boxConstantMissing : List String :=
  [ "absolute bounds on S = log s^Q and T = l*_mod * log s^<= (Section1 estimates, not consolidated)",
    "exact identification D = log d^K versus logdf = log d + log f",
    "uniform finite-l epsilon bookkeeping if claiming the number 6",
    "q-side dictionary Q = log q (qPilot reading)" ]

theorem boxConstantRows_length : boxConstantRows.length = 6 := rfl
theorem boxConstantMissing_length : boxConstantMissing.length = 4 := rfl

#print axioms boxRatio_eq_eps
#print axioms paper_procession_le

end LeanFormal.IUT.XiFPaper.Mzk1BoxConstantAuditActual
