print("sage ok")
try:
    from sage.databases.cremona import cremona_curves
    E = list(cremona_curves(11))
    print("cremona 11", len(E), E[0].ainvs())
except Exception as e:
    print("cremona error", type(e).__name__, e)
try:
    from sage.databases.cremona import EllipticCurveDatabase
    db = EllipticCurveDatabase()
    print("db", db)
except Exception as e:
    print("db error", type(e).__name__, e)
