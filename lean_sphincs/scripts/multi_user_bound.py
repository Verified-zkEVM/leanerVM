#!/usr/bin/env python3
"""Evaluates the proved multi-user bound `Multi.multiSmall` (`Sphincs/MultiBound.lean`) in exact
rational arithmetic, at the certificate constants of `b = 26` (`full`) and `b = 20` (`pruned20`).

`B` (`H0.small_bXX.B`) and `c0 = 2^b En / 2` (`H0.near_bXX.En`) are scaled by `2^128` and rounded
down to the digits printed by `#eval` of `LifetimeCertificates`; the evaluation itself is not checked
by Lean. Prints `multiSmall n q * 2^128 / q` and the ratio to `n q / 2^127`.
"""
from fractions import Fraction as Fr
from math import comb, log2
def bound(n,q,b,N,qh,rho,B128,c0128):
    T=Fr(2)**128
    kc=226*2**b+2*(26-b)
    M=2*(q+307); Mp=max(M-kc,0)
    kap=2-rho+Fr(qh)/T+Fr(N)*123/(2**b*2**15)
    cc=kap*c0128/T
    B=B128/T
    nu=1/T
    landing=Fr(1,2**(26-b))
    rateS=(1/T)*((1-landing)+1)
    k=(rho/T)/(1-M*rho/T)
    pc=Fr(1,2**256)*2+Fr(1,2**128)
    main=k*(q*(1+n*n*pc)+n*(309+3*Fr(M*M,2**256)+(q+307)*3*Fr(M,2**256)))
    rest=Mp*B+nu*comb(Mp,2)*rateS+Mp*nu*Mp*cc
    fail=((Mp+N)+Mp*nu*(Mp+N))*Fr(1,2**201)
    per=rest+2*Fr(1,2**201)+fail+3*Fr(M,2**256)
    return main+n*per
sets={'full':(26,1383000000,250752950924986904089568310569467904,Fr(240268700805,137438953472),Fr(996025098,10**12),Fr(1016789624,10**6)),
'pruned20':(20,26030000,558871528355207643822193711415033856,Fr(1027384687483,549755813888),Fr(1793371115,10**12),Fr(339091854,10**6))}
T=2**128
for nm,(b,N,qh,rho,B,c0) in sets.items():
    kc=226*2**b+2*(26-b)
    qmax=(qh+kc)//2-307
    print(nm,"rho",float(rho),"qmax=2^%.2f"%log2(qmax))
    for n in [1,2**10,2**20,2**32]:
        for q in [2**40,2**64,2**80,2**100,2**110,qmax]:
            v=bound(n,q,b,N,qh,rho,B,c0)
            old=Fr(n*q,2**127)
            print("  n=2^%d q=2^%.1f  eps*2^128/q=%.6f  (n q/2^127)*2^128/q=%.1f  ratio=%.4g"%(int(log2(n)),log2(q),float(v*T/q),float(old*T/q),float(v/old)))
for nm,(b,N,qh,rho,B,c0) in sets.items():
    kc=226*2**b+2*(26-b); qmax=(qh+kc)//2-307
    lo,hi=2**100,qmax
    for _ in range(200):
        mid=(lo+hi)//2
        if bound(1,mid,b,N,qh,rho,B,c0) < Fr(mid,2**127): lo=mid
        else: hi=mid
    print(nm,"n=1 crossing at 2^%.2f"%log2(lo))
    for n in [2**10,2**20]:
        lo,hi=2**100,qmax
        if bound(n,qmax,b,N,qh,rho,B,c0) < Fr(n*qmax,2**127): print(nm,n,"below up to qmax"); continue
