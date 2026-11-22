import time
from sage.databases.cremona import CremonaDatabase
db=CremonaDatabase()
Es=[]; N=1
while len(Es)<50 and N<=200:
    for lab,dat in db.allcurves(N).items():
        E=EllipticCurve(dat[0])
        if E.is_semistable(): Es.append(E)
    N+=1
print("n",len(Es))
t=time.time(); ds=[E.modular_degree() for E in Es[:10]]; print("10 deg",time.time()-t,ds)
