lemma omega_step_algebra {a b c d e f g Bv Ev Fv : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hg : g ≠ 0)
    (hf : f * g = b ^ 2 * a * Fv - c * a * Ev ^ 2)
    (hd : d * g = c ^ 2 * b * Ev - Bv * b * a ^ 2)
    (he : e = Ev * b ^ 3 - c * a ^ 3)
    (hrel : b ^ 2 * c * Fv - a ^ 2 * Bv * Ev = g ^ 2 * e) :
    f / a ^ 4 = - (d / b ^ 4) + (g - d / b ^ 4) * (e / (a ^ 3 * c)) := by
  have hE0 : f * b ^ 4 * c + d * a ^ 4 * c - g * e * a * b ^ 4 + d * e * a = 0 := by
    have h1 : (f * b ^ 4 * c + d * a ^ 4 * c - g * e * a * b ^ 4 + d * e * a) * g = 0 := by
      rw [show (f * b ^ 4 * c + d * a ^ 4 * c - g * e * a * b ^ 4 + d * e * a) * g =
          (f * g) * b ^ 4 * c + (d * g) * a ^ 4 * c - (g ^ 2 * e) * a * b ^ 4 +
            (d * g) * e * a by ring]
      rw [hf, hd, hrel, he]
      ring
    exact (mul_eq_zero.mp h1).resolve_right hg
  field_simp [ha, hb, hc, hg]
  linear_combination hE0

