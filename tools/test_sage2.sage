import sage.databases.cremona as c
print([x for x in dir(c) if 'remona' in x or 'Curve' in x or 'Database' in x])
try:
    print(c.CremonaDatabase())
except Exception as e:
    print("CremonaDatabase error", type(e).__name__, e)
try:
    E=EllipticCurve('11a1'); print("E11a1",E.ainvs(),E.conductor(),E.discriminant())
except Exception as e:
    print("Ec error", type(e).__name__, e)
