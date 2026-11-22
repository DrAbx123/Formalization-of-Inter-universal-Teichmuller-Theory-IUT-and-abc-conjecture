import json, traceback
from sage.all import *
rows=json.load(open("coord/b1_curves_500.json"))
row=[r for r in rows if r["label"]=="113a1"][0]
N=int(row["N"]); E=EllipticCurve(row["label"]); F=CuspForms(Gamma0(N),2).newforms(names='a')
print("nforms",len(F))
for i,f in enumerate(F):
    co=f.q_expansion(60); print("form",i,"co2",co[2],type(co[2]),"parent",co[2].parent())
    try: print("intco2",int(co[2]),"intco3",int(co[3]))
    except Exception as e: print("int err",e)
try:
    print("curve ap",E.ap(2),E.ap(3),E.ap(5))
except Exception as e: print("ap err",e)
