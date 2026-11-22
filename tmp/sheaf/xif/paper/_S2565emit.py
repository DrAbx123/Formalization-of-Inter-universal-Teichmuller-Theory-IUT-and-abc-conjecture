
import re
from sympy import Poly, GF, symbols

path = r"D:/lean/tmp/sheaf/xif/paper/S2554Mod613ChainDataActual.lean"
src = open(path, encoding="utf-8").read()
p = 613
x = symbols("x")

def parse_poly(body):
    d = {}
    for t in body.split("+"):
        t = t.strip()
        for pat, fn in ((r"C\s*(\d+)\s*\*\s*X\s*\^\s*(\d+)", 2), (r"C\s*(\d+)\s*\*\s*X", 1)):
            m = re.fullmatch(pat, t)
            if m:
                if fn == 2:
                    c, e = int(m.group(1)), int(m.group(2)); d[e] = (d.get(e,0)+c)%p
                else:
                    d[1] = (d.get(1,0)+int(m.group(1)))%p
                break
        else:
            m = re.fullmatch(r"C\s*(\d+)", t)
            if m: d[0] = (d.get(0,0)+int(m.group(1)))%p; continue
            m = re.fullmatch(r"X\s*\^\s*(\d+)", t)
            if m: d[int(m.group(1))] = (d.get(int(m.group(1)),0)+1)%p; continue
            m = re.fullmatch(r"X", t)
            if m: d[1] = (d.get(1,0)+1)%p; continue
            raise ValueError("bad term: "+t)
    return d

data = {}
for line in src.splitlines():
    m = re.match(r"def (G|T\d+) : \(ZMod 613\)\[X\] := (.*)", line)
    if m:
        data[m.group(1)] = parse_poly(m.group(2))

def to_poly(d):
    return Poly(sum(c*x**e for e,c in d.items()), x, domain=GF(p))
P = {k: to_poly(v) for k,v in data.items()}

def fmt(d):
    terms = []
    for e in sorted(d):
        c = d[e] % p
        if c == 0: continue
        if e == 0: terms.append("C %d" % c)
        elif e == 1: terms.append("C %d * X" % c)
        else: terms.append("C %d * X ^ %d" % (c, e))
    return " + ".join(terms)

def dense(poly):
    if poly.is_zero: return {}
    coeffs = poly.all_coeffs()
    n = len(coeffs)-1
    return {n-i: int(c) % p for i,c in enumerate(coeffs)}

quos = {}
for k in range(5,9):
    C = P["T%d" % k].compose(P["T1"])
    Q = C - P["T%d" % (k+1)]
    quo, rem = divmod(Q, P["G"])
    assert rem.is_zero and quo.degree() == 109, (k, rem, quo.degree())
    quos[k] = dense(quo)

hdr = '''/-
S2565: second half of the composition chain for the degree-12 polynomial G.

For k = 5, 6, 7, 8 we prove
  G divides (T_k).comp T1 - T_{k+1}
by exhibiting the explicit quotient S_k of degree 109, obtained by dividing
(T_k).comp T1 - T_{k+1} by G over GF(613).

The polynomial identity  G * S_k = (T_k).comp T1 - T_{k+1}  is proved by
checking equality at the 122 points 0, ..., 121 of ZMod 613: both sides have
natDegree at most 121, and ZMod 613 is a domain, so a polynomial of degree
< 122 vanishing at 122 distinct points is zero
(Polynomial.eq_of_natDegree_lt_card_of_eval_eq).
Each point evaluation is a closed computation in ZMod 613 closed by decide.

No axioms, no sorry, no native_decide.
-/

import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

/-! ### The explicit quotients -/
'''

body = []
for k in range(5,9):
    body.append("/-- Explicit quotient of (T%d).comp T1 - T%d by G. -/" % (k, k+1))
    body.append("def S%d : (ZMod 613)[X] :=" % k)
    body.append("  " + fmt(quos[k]))
    body.append("")

points = '''/-! ## The evaluation points 0, ..., 121 of ZMod 613. -/

lemma point_injection :
    Function.Injective (fun i : Fin 122 => ((i : \u2115) : ZMod 613)) := by
  intro i j h
  have hi : (i : \u2115) < 613 := by have := i.isLt; omega
  have hj : (j : \u2115) < 613 := by have := j.isLt; omega
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  exact Fin.ext h

/-! ## Degree bounds -/

lemma natDegree_G_le : G.natDegree \u2264 12 := by
  unfold G
  compute_degree!

lemma natDegree_T1_le : T1.natDegree \u2264 11 := by
  unfold T1
  compute_degree!
'''

deg = [points]
for k in range(5,10):
    deg.append("")
    deg.append("lemma natDegree_T%d_le : T%d.natDegree \u2264 11 := by" % (k,k))
    deg.append("  unfold T%d" % k)
    deg.append("  compute_degree!")
for k in range(5,9):
    deg.append("")
    deg.append("lemma natDegree_S%d_le : S%d.natDegree \u2264 109 := by" % (k,k))
    deg.append("  unfold S%d" % k)
    deg.append("  compute_degree!")
for k in range(5,9):
    deg.append("")
    deg.append("lemma natDegree_G_mul_S%d_le : (G * S%d).natDegree \u2264 121 := by" % (k,k))
    deg.append("  calc (G * S%d).natDegree \u2264 G.natDegree + S%d.natDegree :=" % (k,k))
    deg.append("        Polynomial.natDegree_mul_le")
    deg.append("    _ \u2264 12 + 109 := Nat.add_le_add natDegree_G_le natDegree_S%d_le" % k)
    deg.append("    _ = 121 := by norm_num")
for k in range(5,9):
    deg.append("")
    deg.append("lemma natDegree_comp_T%d_le : (T%d.comp T1).natDegree \u2264 121 := by" % (k,k))
    deg.append("  calc (T%d.comp T1).natDegree \u2264 T%d.natDegree * T1.natDegree :=" % (k,k))
    deg.append("        Polynomial.natDegree_comp_le")
    deg.append("    _ \u2264 11 * 11 := Nat.mul_le_mul natDegree_T%d_le natDegree_T1_le" % k)
    deg.append("    _ = 121 := by norm_num")
    deg.append("")
    deg.append("lemma natDegree_R%d_le : (T%d.comp T1 - T%d).natDegree \u2264 121 := by" % (k,k,k+1))
    deg.append("  calc (T%d.comp T1 - T%d).natDegree \u2264 max (T%d.comp T1).natDegree T%d.natDegree :=" % (k,k+1,k,k+1))
    deg.append("        Polynomial.natDegree_sub_le _ _")
    deg.append("    _ \u2264 121 := max_le natDegree_comp_T%d_le (by have := natDegree_T%d_le; omega)" % (k,k+1))

ident = ["", "/-! ## The identities and the divisibility -/"]
for k in range(5,9):
    ident.append("")
    ident.append("/-- S%d really is the quotient of (T%d).comp T1 - T%d by G. -/" % (k,k,k+1))
    ident.append("theorem identity_%d : G * S%d = T%d.comp T1 - T%d := by" % (k,k,k,k+1))
    ident.append("  haveI : Fact (Nat.Prime 613) := \u27e8by norm_num\u27e9")
    ident.append("  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq")
    ident.append("    (f := fun i : Fin 122 => ((i : \u2115) : ZMod 613)) point_injection ?_ ?_")
    ident.append("  \u00b7 intro i")
    ident.append("    fin_cases i <;>")
    ident.append("      (simp [G, S%d, T%d, T%d, T1," % (k,k,k+1))
    ident.append("        Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,")
    ident.append("        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_comp] <;>")
    ident.append("        decide)")
    ident.append("  \u00b7 simp only [Fintype.card_fin]")
    ident.append("    have h1 := natDegree_G_mul_S%d_le" % k)
    ident.append("    have h2 := natDegree_R%d_le" % k)
    ident.append("    omega")
    ident.append("")
    ident.append("/-- G divides (T%d).comp T1 - T%d. -/" % (k,k+1))
    ident.append("theorem chain_dvd_%d : G \u2223 T%d.comp T1 - T%d := \u27e8S%d, identity_%d.symm\u27e9" % (k,k,k+1,k,k))

tail = "\nend LeanFormal.IUT.XiFPaper.S2565ChainComp2Actual\n\nend\n"
out = hdr + "\n" + "\n".join(body) + "\n" + "\n".join(deg) + "\n".join(ident) + tail
open(r"D:/lean/tmp/sheaf/xif/paper/S2565ChainComp2Actual.lean","w",encoding="utf-8").write(out)
print("written", len(out))
