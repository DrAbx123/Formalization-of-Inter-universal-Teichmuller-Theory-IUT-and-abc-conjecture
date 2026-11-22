import tmp.sheaf.xif.paper.S2141D5FactorizationFieldsActual
open Polynomial
open LeanFormal.IUT.XiFPaper.S2141D5FactorizationFieldsActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
example : S2141Factor10 = C (4 : ZMod 29) * S2132Factor10 := by
  unfold S2141Factor10 S2132Factor10
  unfold _root_.f
  ext n
  by_cases hn : n ≤ 10
  · interval_cases n <;> simp [coeff_mul, coeff_C, coeff_X_pow] <;> reduce_mod_char
  · have h1 : (S2132Factor10).coeff n * 4 = 0 := by
      rw [show S2132Factor10 = _root_.f from rfl]
      simp only [S2132Factor10]
      sorry
    sorry
