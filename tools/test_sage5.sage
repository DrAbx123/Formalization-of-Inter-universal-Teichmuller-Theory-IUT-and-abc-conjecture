from sage.databases.cremona import CremonaDatabase
db=CremonaDatabase()
E=EllipticCurve([0,-1,1,-10,-20])
print("semistable",E.is_semistable())
print("tamagawa",E.tamagawa_numbers())
print("torsion",E.torsion_subgroup().order(), list(E.torsion_points())[:5])
print("deg",E.modular_degree())
print("ap",[E.ap(p) for p in [2,3,5,7,11]])
print("conductor",E.conductor(),"disc",E.discriminant())
ncurves=0; nsemi=0
for N in range(1,2001):
    d=db.allcurves(N)
    for lab,dat in d.items():
        ncurves+=1
        Ex=EllipticCurve(dat[0])
        if Ex.is_semistable(): nsemi+=1
print("curves",ncurves,"semi",nsemi)
