
import json
D = json.load(open(r"D:\lean\tmp\sheaf\xif\paper\_comp3_data.json"))

def to_lean(a):
    parts=[]
    for e,c in enumerate(a):
        if c==0: continue
        if e==0: parts.append(f"C {c}")
        elif e==1: parts.append(f"C {c} * X")
        else: parts.append(f"C {c} * X ^ {e}")
    return " + ".join(parts) if parts else "C 0"

lines = []
lines.append("import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual")
lines.append("")
lines.append("noncomputable section")
lines.append("set_option maxHeartbeats 16000000")
lines.append("set_option maxRecDepth 100000")
lines.append("open Polynomial")
lines.append("")
lines.append("namespace LeanFormal.IUT.XiFPaper.S2565ProbeA")
lines.append("")
lines.append("open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual")
lines.append("")
for i in range(2,12):
    lines.append(f"def T1pow{i} : (ZMod 613)[X] := {to_lean(D['Q'][str(i)])}")
lines.append("")
for i in range(2,12):
    lines.append(f"axiom T1_pow{i} : T1 ^ {i} = T1pow{i}")
lines.append("")
lines.append(f"def S9 : (ZMod 613)[X] := {to_lean(D['S']['9'])}")
lines.append("")
lines.append("example : (G * S9).coeff 121 = (T9.comp T1 - T10).coeff 121 := by")
lines.append("  simp [G, S9, T9, T10, T1, " + ", ".join(f"T1pow{i}" for i in range(2,12)) + ",")
lines.append("    " + ", ".join(f"T1_pow{i}" for i in range(2,12)) + ",")
lines.append("    Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C,")
lines.append("    Polynomial.coeff_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,")
lines.append("    Polynomial.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> norm_num")
lines.append("")
lines.append("end LeanFormal.IUT.XiFPaper.S2565ProbeA")
open(r"D:\lean\tmp\sheaf\xif\paper\_probeA.lean","w",encoding="utf-8").write("\n".join(lines)+"\n")
print("written", len(lines))
