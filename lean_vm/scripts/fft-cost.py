"""K-multiplication and inversion counts of the planned additive FFT over K
(lean_vm/LeanVM/Protocol/Extraction/Fast/FFT/{Basis,Plan,Additive}.lean), mirroring the definitions:
every K `*` the definitions execute is counted; additions are not. Run: python3 -I fft-cost.py"""
# Exact K-multiplication / inversion counts of the planned additive FFT (Fast/FFT/Plan.lean,
# Basis.lean, Additive.lean), mirroring the definitions' evaluation (every K `*` executed).
import math
def evalLin(size): return 2*size            # evalLinFrom: s_o*a and a*a per term
def table(j):                               # tableUpTo j
    if j==0: return 0
    m=evalLin(1)                            # linData 0
    for J in range(1,j):                    # step to level J: s of size J
        m+= (2*J+1) + evalLin(J+1)          # linStep: J squarings + (J+1) beta-products; evalLin
    return m
def batchInv(n): return 3*n                 # p*b, r2*p, r2*b per entry; 1 inversion
def twiddles(j): return sum((j-i-1)*(evalLin(i+1)+1) for i in range(j))  # adds by doubling: free
def plan(j): return table(j)+batchInv(j)+twiddles(j), (1 if j>0 else 0)
def plan_adds(j): return sum(2**(j-i-1)-1 for i in range(j))  # spanTable additions
def conv(j):                                # toNovelRec / fromNovelRec (exact, see count.py)
    return sum(2**(j-i-1)*(i+1)*2**i for i in range(j))   # = N j(j+1)/4
def fwdNTT(j): return j*2**(j-1)            # fwdStageFast: one product per butterfly per stage
def invNTT(j): return j*2**(j-1)            # invStageWith: one product per pair per stage
def fwdP(j): return conv(j)+fwdNTT(j)
def invP(j): return conv(j)+invNTT(j)
def product(j): return fwdP(j)*2 + 2**j + invP(j)       # mulVia transform branch, plan separate
print("j  plan_mults plan_inv  fwdP/N   invP/N   product/N  (N=2^j)")
for j in [1,2,4,6,8,10,12,16,20,24,28,30,32,35,36,40]:
    N=2**j; pm,pi=plan(j)
    assert conv(j)==N*j*(j+1)//4
    print("%2d %9d %3d  %8.2f %8.2f %9.2f"%(j,pm,pi,fwdP(j)/N,invP(j)/N,product(j)/N))
print("closed forms: conv = N*j*(j+1)/4; fwdP = invP = N*(j^2+3j)/4;")
print("  product = N*(3j^2+9j+4)/4 (+ plan); plan = table + 3j + twiddles, 1 inversion")
for j in [1,4,10,36]:
    assert product(j)==2**j*(3*j*j+9*j+4)//4, j
    assert fwdP(j)==invP(j)==2**j*(j*j+3*j)//4, j
# matrix product (evalmat): (r*s + s*t) fwdP + r*t invP + r*s*t*N pointwise, + 1 plan
r=2077; s=2077; t=2077
for j in [5,10,20,35]:
    N=2**j
    print("j=%d  square r=2077: transforms 2^%.2f, pointwise 2^%.2f, plan %d mults"%(j, math.log2((r*s+s*t)*fwdP(j)+r*t*invP(j)), math.log2(r*s*t*N), plan(j)[0]))

# ---- the in-place conversions (Fast/FFT/Convert.lean): array entries and loop iterations per
# level, against the recursive ones (toNovelRecP, fromNovelRecP) they replace.
def asc_sum(i, n):        # over e < n: sumAsc's iterations (from t = 0, i terms, stop at 2^t > e)
    prod = sum(max(0, n - 2**t) for t in range(i))
    stops = min(n, 2**(i-1)) if i >= 1 else 0      # e < 2^(i-1): one failing check
    return prod + stops
def desc_sum(i, n):       # over x < n: sumDesc's iterations (from t = i-1 down, stop at 2^t <= x)
    prod = sum(min(n, 2**t) for t in range(i))
    stops = (n - 1) if (i >= 1 and n >= 1) else 0   # x >= 1: one failing check
    return prod + stops
def to_level(i):          # per block of 2^(i+1): (array entries, loop iterations, K products)
    H = 2**i; h = H//2
    return H + 2*H, desc_sum(i, h) + asc_sum(i, H), (i+1)*H
def from_level(i):
    H = 2**i
    return 2*H, asc_sum(i, H) + desc_sum(i, H), (i+1)*H
def old_to_level(i):      # qtop, qlo, ++, divRem, scaleArr, the recursion's ++ ; linCoeffP: i per entry
    H = 2**i; h = H//2
    return 6*H, i*(h + H), (i+1)*H
def old_from_level(i):    # two slices, scaleArr, mulAddW ; linCoeffP: i per entry of mulAddW
    H = 2**i
    return 5*H, i*2*H, (i+1)*H
def per_conv(level, j):
    N = 2**j; tot = [0, 0, 0]
    for i in range(j):
        e, it, m = level(i); blocks = N // 2**(i+1)
        tot = [tot[0]+blocks*e, tot[1]+blocks*it, tot[2]+blocks*m]
    return [x / (j*N) for x in tot]
print()
print("conversions, per j*2^j:   entries  iterations  K-products   (old: entries iterations)")
for j in [6, 10, 16, 20, 30, 36]:
    a = per_conv(to_level, j); b = per_conv(old_to_level, j)
    c = per_conv(from_level, j); d = per_conv(old_from_level, j)
    print("j=%2d toNovel   %5.2f  %8.2f  %8.2f      (%5.2f  %8.2f)" % (j, a[0], a[1], a[2], b[0], b[1]))
    print("     fromNovel %5.2f  %8.2f  %8.2f      (%5.2f  %8.2f)" % (c[0], c[1], c[2], d[0], d[1]))
