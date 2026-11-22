import cmath, math
import numpy as np

def beta(z):
    return 4*z/(1+z)**2

def beta_prime(z):
    return 4*(1-z)/(1+z)**3

def iterate(z,n):
    for _ in range(n):
        z=beta(z)
    return z

def I_r(n,r,N=20000):
    th=np.linspace(0,2*np.pi,N,endpoint=False)
    z=r*np.exp(1j*th)
    vals=np.array([iterate(zz,n) for zz in z])
    logs=np.log(np.abs(vals))
    pos=np.maximum(logs,0.0)
    return float(np.trapezoid(pos,th)/(2*np.pi))

for n in range(1,7):
    print(n, 4**n, I_r(n,0.99), I_r(n,0.999))
print("ratio")
for n in range(1,7):
    print(n, I_r(n,0.99), I_r(n,0.999))
