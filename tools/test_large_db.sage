from sage.databases.cremona import LargeCremonaDatabase
try:
    db=LargeCremonaDatabase()
    print("large",db.conductor_range(),db.largest_conductor())
except Exception as e: print("large err",type(e).__name__,e)
