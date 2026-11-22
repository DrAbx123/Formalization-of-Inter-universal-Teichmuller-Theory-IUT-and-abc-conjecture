from sage.databases.cremona import CremonaDatabase
db=CremonaDatabase()
for fn in ['curves','allcurves','list','isogeny_classes']:
    try:
        x=getattr(db,fn)(11)
        print(fn,type(x),str(x)[:500])
    except Exception as e: print(fn,'err',type(e).__name__,e)
print('conductor_range',db.conductor_range())
