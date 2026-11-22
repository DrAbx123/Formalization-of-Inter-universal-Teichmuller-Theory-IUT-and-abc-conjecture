from sage.databases.cremona import CremonaDatabase
db=CremonaDatabase()
print([x for x in dir(db) if not x.startswith('_')][:80])
try:
    print("allcurves",db.allcurves(11)[:2])
except Exception as e: print("allcurves err",type(e).__name__,e)
try:
    print("curves",db.curves(11)[:2])
except Exception as e: print("curves err",type(e).__name__,e)
try:
    print("N",db.number_of_curves(11))
except Exception as e: print("num err",type(e).__name__,e)
