import Mathlib

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2558S0Part2Actual

/-- Coefficients 161..240 of the quotient S0. -/
def S0_2 : (ZMod 613)[X] := C 122 * X ^ 161 + C 379 * X ^ 162 + C 221 * X ^ 163 + C 373 * X ^ 164 + C 182 * X ^ 165 + C 341 * X ^ 166 + C 406 * X ^ 167 + C 356 * X ^ 168 + C 395 * X ^ 169 + C 403 * X ^ 170 + C 278 * X ^ 171 + C 253 * X ^ 172 + C 24 * X ^ 173 + C 170 * X ^ 174 + C 438 * X ^ 175 + C 256 * X ^ 176 + C 341 * X ^ 177 + C 453 * X ^ 178 + C 198 * X ^ 179 + C 283 * X ^ 180 + C 343 * X ^ 181 + C 312 * X ^ 182 + C 33 * X ^ 183 + C 136 * X ^ 184 + C 427 * X ^ 185 + C 9 * X ^ 187 + C 154 * X ^ 188 + C 63 * X ^ 189 + C 80 * X ^ 190 + C 91 * X ^ 191 + C 405 * X ^ 192 + C 539 * X ^ 193 + C 603 * X ^ 194 + C 244 * X ^ 195 + C 609 * X ^ 196 + C 583 * X ^ 197 + C 384 * X ^ 198 + C 287 * X ^ 199 + C 265 * X ^ 200 + C 552 * X ^ 201 + C 9 * X ^ 202 + C 405 * X ^ 203 + C 75 * X ^ 204 + C 285 * X ^ 205 + C 62 * X ^ 206 + C 245 * X ^ 207 + C 93 * X ^ 208 + C 574 * X ^ 209 + C 205 * X ^ 210 + C 576 * X ^ 211 + C 490 * X ^ 212 + C 29 * X ^ 213 + C 420 * X ^ 214 + C 186 * X ^ 215 + C 247 * X ^ 216 + C 65 * X ^ 217 + C 405 * X ^ 218 + C 410 * X ^ 219 + C 193 * X ^ 220 + C 55 * X ^ 221 + C 544 * X ^ 222 + C 470 * X ^ 223 + C 276 * X ^ 224 + C 180 * X ^ 225 + C 604 * X ^ 226 + C 117 * X ^ 227 + C 314 * X ^ 228 + C 417 * X ^ 229 + C 477 * X ^ 230 + C 386 * X ^ 231 + C 369 * X ^ 232 + C 110 * X ^ 233 + C 172 * X ^ 234 + C 358 * X ^ 235 + C 512 * X ^ 236 + C 397 * X ^ 237 + C 431 * X ^ 238 + C 456 * X ^ 239 + C 455 * X ^ 240

theorem S0_2_natDegree_le : S0_2.natDegree ≤ 240 := by
  unfold S0_2
  compute_degree!

end LeanFormal.IUT.XiFPaper.S2558S0Part2Actual

end