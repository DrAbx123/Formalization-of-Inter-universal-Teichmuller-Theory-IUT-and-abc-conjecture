import json, traceback
exec(open("tools/b1_exact_snf.sage").read().split("out=[];")[0])
row=[r for r in rows if r["label"]=="113a1"][0]
try:
    r=exact(row); print(r)
except Exception as e:
    traceback.print_exc()
