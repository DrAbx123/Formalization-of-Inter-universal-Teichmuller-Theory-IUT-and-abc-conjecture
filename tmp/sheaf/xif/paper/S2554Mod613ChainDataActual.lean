import tmp.sheaf.xif.paper.S2553Mod613DegreeActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual

/-- The monic normalization of F613. -/
def G : (ZMod 613)[X] := C 451 + C 389 * X ^ 2 + C 412 * X ^ 3 + C 251 * X ^ 4 + C 501 * X ^ 5 + C 586 * X ^ 6 + C 82 * X ^ 7 + C 551 * X ^ 8 + C 327 * X ^ 9 + C 210 * X ^ 10 + C 272 * X ^ 11 + C 1 * X ^ 12

theorem G_eq_scaled : G = C (168 : ZMod 613) * F613 := by
  ext n
  by_cases hn : n ≤ 12
  · interval_cases n <;> (simp [G, F613] <;> decide)
  · have h1 : G.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : G.natDegree ≤ 12 := by unfold G; compute_degree!
      omega
    have h2 : (C (168 : ZMod 613) * F613).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : (C (168 : ZMod 613) * F613).natDegree ≤ 12 := by unfold F613; compute_degree!
      omega
    rw [h1, h2]

def T1 : (ZMod 613)[X] := C 188 + C 160 * X + C 530 * X ^ 2 + C 308 * X ^ 3 + C 530 * X ^ 4 + C 279 * X ^ 5 + C 7 * X ^ 6 + C 567 * X ^ 7 + C 432 * X ^ 8 + C 288 * X ^ 9 + C 442 * X ^ 10 + C 272 * X ^ 11
def T2 : (ZMod 613)[X] := C 355 + C 93 * X + C 539 * X ^ 2 + C 217 * X ^ 3 + C 396 * X ^ 4 + C 278 * X ^ 5 + C 226 * X ^ 6 + C 130 * X ^ 7 + C 271 * X ^ 8 + C 126 * X ^ 9 + C 43 * X ^ 10 + C 398 * X ^ 11
def T3 : (ZMod 613)[X] := C 299 + C 602 * X + C 530 * X ^ 2 + C 47 * X ^ 3 + C 332 * X ^ 4 + C 190 * X ^ 5 + C 121 * X ^ 6 + C 293 * X ^ 7 + C 268 * X ^ 8 + C 391 * X ^ 9 + C 329 * X ^ 10 + C 375 * X ^ 11
def T4 : (ZMod 613)[X] := C 304 + C 381 * X + C 485 * X ^ 2 + C 30 * X ^ 3 + C 70 * X ^ 4 + C 493 * X ^ 5 + C 560 * X ^ 6 + C 423 * X ^ 7 + C 252 * X ^ 8 + C 575 * X ^ 9 + C 186 * X ^ 10 + C 15 * X ^ 11
def T5 : (ZMod 613)[X] := C 110 + C 342 * X + C 437 * X ^ 2 + C 166 * X ^ 3 + C 448 * X ^ 4 + C 312 * X ^ 5 + C 99 * X ^ 6 + C 53 * X ^ 7 + C 125 * X ^ 8 + C 334 * X ^ 9 + C 132 * X ^ 10 + C 576 * X ^ 11
def T6 : (ZMod 613)[X] := C 449 + C 608 * X + C 97 * X ^ 2 + C 88 * X ^ 3 + C 311 * X ^ 4 + C 248 * X ^ 5 + C 430 * X ^ 6 + C 477 * X ^ 7 + C 162 * X ^ 8 + C 280 * X ^ 9 + C 259 * X ^ 10 + C 580 * X ^ 11
def T7 : (ZMod 613)[X] := C 594 + C 447 * X + C 417 * X ^ 2 + C 577 * X ^ 3 + C 563 * X ^ 4 + C 236 * X ^ 5 + C 103 * X ^ 6 + C 378 * X ^ 7 + C 126 * X ^ 8 + C 427 * X ^ 9 + C 242 * X ^ 10 + C 412 * X ^ 11
def T8 : (ZMod 613)[X] := C 406 + C 611 * X + C 186 * X ^ 2 + C 143 * X ^ 3 + C 554 * X ^ 4 + C 117 * X ^ 5 + C 286 * X ^ 6 + C 87 * X ^ 7 + C 526 * X ^ 8 + C 402 * X ^ 9 + C 495 * X ^ 10 + C 180 * X ^ 11
def T9 : (ZMod 613)[X] := C 533 + C 297 * X + C 483 * X ^ 2 + C 536 * X ^ 3 + C 11 * X ^ 4 + C 273 * X ^ 5 + C 352 * X ^ 6 + C 303 * X ^ 7 + C 338 * X ^ 8 + C 64 * X ^ 9 + C 403 * X ^ 10 + C 32 * X ^ 11
def T10 : (ZMod 613)[X] := C 14 + C 405 * X + C 548 * X ^ 2 + C 441 * X ^ 3 + C 289 * X ^ 4 + C 364 * X ^ 5 + C 234 * X ^ 6 + C 186 * X ^ 7 + C 463 * X ^ 8 + C 151 * X ^ 9 + C 232 * X ^ 10 + C 49 * X ^ 11
def T11 : (ZMod 613)[X] := C 154 + C 344 * X + C 39 * X ^ 2 + C 512 * X ^ 3 + C 174 * X ^ 4 + C 275 * X ^ 5 + C 34 * X ^ 6 + C 168 * X ^ 7 + C 102 * X ^ 8 + C 27 * X ^ 9 + C 302 * X ^ 10 + C 176 * X ^ 11
def T12 : (ZMod 613)[X] := X

theorem T12_eq_X : T12 = X := rfl

/-- The exact still-missing irreducibility of the monic normalization. -/
def S2554Mod613IrreducibleRequired : Prop := Irreducible G

end LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

end