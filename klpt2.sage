from klpt_panny import *
from random import randint

load('sspecppas.sage')

def KLPT2(g1,g2,L=2,target_e0=100,verbose=True,step_by_step=False):
    while True:
        min_e2 = 0
        if verbose:
            print(f"target_e0 = {target_e0}")

        (s,r),(r̄,t) = g1
        assert ct(r) == r̄, f"[Error] KLPT2: g1 is not Hermitian."
        if verbose:
            print("\n1A. Starting get_acś.")
        a,c,ś = get_acś(g1, L, verbose)
        ā,c̄ = ct(a), ct(c)
        if verbose:
            print("1A. Completed get_acś.")
            print(f"a = {a}")
            print(f"c = {c}")
            print(f"s' = {ś}")
            if not ś.is_prime(): print("Warning: s' is not prime")
            print("\n1B. Starting get_bde0.")
        if step_by_step: breakpoint()
        b,d,e0 = get_bde0(a,c,L,target_e0,verbose)
        u1 = Matrix(B,2,2,[a,b,c,d])
        ūgu = ct(u1)*g1*u1
        if verbose:
            print("1B. Completed get_bde0.")
            print(f"b = {b}")
            print(f"d = {d}")
            print(f"e0 = {e0}")
            print("\n1C. Starting get_αǵ.")
        if step_by_step: breakpoint()
        α1, ǵ1 = get_αǵ(ūgu, L, verbose)
        ŕ = ǵ1[0][1]
        rn_ŕ = ZZ(rn(ŕ))
        if verbose:
            print("1C. Completed get_αǵ.")
            print(f"α = {α1}")
        rn_ǵ1 = ZZ(rn(ǵ1))
        assert rn_ǵ1.is_prime_power(), f"[Error] KLPT2: 𝒩(g1') = {rn_ǵ1} is not a prime power."
        if verbose:
            print(f"𝒩(g1') = {factor(rn_ǵ1)}")
        if step_by_step: breakpoint()
        
        while True:
            if verbose:
                print("\n1D. Starting get_áće2.")
            á,ć,e2 = get_áće2(ǵ1, L, None, min_e2, verbose)
            if e2 == None:
                print(f"[Error] KLPT2: Could not find á and ć using e2 = {e2}. Restarting.")
                break
            min_e2 = e2 + 1
            if verbose:
                print("1D. Completed get_áće2.")
                print(f"a' = {á}")
                print(f"c' = {ć}")
                print(f"e2 = {e2}")
                print("\n1E. Starting get_bde0.")
            if step_by_step: breakpoint()
            for trial_e0 in range(e0-4, e0+12):
                b́,d́,e0_1 = get_bde0(á,ć,L,trial_e0,verbose)
                if verbose:
                    print(f"[Debug] get_bde0: Actual e0: {e0} | Input e0: {trial_e0} | Output e0: {e0_1}")
                ú = Matrix(B,2,2,[á,b́,ć,d́])
                U1 = u1*Matrix(B,2,2,[1,α1,0,1])*ú
                if e0_1 == e0: break
            else:
                if verbose:
                    print("[Error] get_bde0: Could not achieve same value of e0.")
                continue
            e1_1 = ZZ(rn(U1)).log(L)
            if e1_1 != 2*e0:
                if verbose:
                    print(f"[Error] KLPT2: e1 ≠ 2*e0.\ne0 = {e0}\n𝒩(u1) = {factor(ZZ(rn(u1)))}\n𝒩(ú) = {factor(ZZ(rn(ú)))}")
                    breakpoint()
                continue
            if verbose:
                print("1E. Completed get_bde0.")
                print(f"b' = {b́}")
                print(f"d' = {d́}")
                print(f"e0' = {e0_1}")
                print(f"\ne1 = {e1_1}")
            if step_by_step: breakpoint()

            (s,r),(r̄,t) = g2
            assert ct(r) == r̄, f"[Error] KLPT2: g2 is not Hermitian."
            if verbose:
                print("\n2A. Starting get_acś.")
            a,c,ś = get_acś(g2, L, verbose)
            if verbose:
                print("2A. Completed get_acś.")
                print(f"a = {a}")
                print(f"c = {c}")
                print(f"s' = {ś}")
                print("\n2B. Starting get_bde0.")
            if step_by_step: breakpoint()
            for trial_e0 in range(e0-4, e0+12):
                b,d,e0_2 = get_bde0(a,c,L,trial_e0,verbose)
                if verbose:
                    print(f"[Debug] get_bde0: Actual e0: {e0} | Input e0: {trial_e0} | Output e0: {e0_2}")
                u2 = Matrix(B,2,2,[a,b,c,d])
                ūgu = ct(u2)*g2*u2
                if e0_2 == e0_1: break
            else:
                if verbose:
                    print("[Error] get_bde0: Could not achieve same value of e0.")
                continue
            if verbose:
                print("2B. Completed get_bde0.")
                print(f"b = {b}")
                print(f"d = {d}")
                print(f"e0 = {e0_2}")
                print("\n2C. Starting get_αǵ.")
            if step_by_step: breakpoint()
            α2, ǵ2 = get_αǵ(ūgu, L, verbose)
            ŕ = ǵ2[0][1]
            rn_ŕ = ZZ(rn(ŕ))
            if verbose:
                print("2C. Completed get_αǵ.")
                print(f"α = {α2}")
            rn_ǵ2 = ZZ(rn(ǵ2))
            assert rn_ǵ2.is_prime_power(), f"[Error] KLPT2: 𝒩(g2') = {rn_ǵ2} is not a prime power."
            if verbose:
                print(f"𝒩(g2') = {factor(rn_ǵ2)}")
                print("\n2D. Starting get_áće2.")
            if step_by_step: breakpoint()
            á,ć,e2 = get_áće2(ǵ2, L, e2, 0, verbose)
            if e2 == None: continue
            if verbose:
                print("2D. Completed get_áće2.")
                print(f"a' = {á}")
                print(f"c' = {ć}")
                print(f"e2 = {e2}")
                print("\n2E. Starting get_bde0.")
            if step_by_step: breakpoint()
            for trial_e0 in range(e0-4, e0+12):
                b́,d́,e0_2 = get_bde0(á,ć,L,trial_e0,verbose)
                if verbose:
                    print(f"[Debug] get_bde0: Actual e0: {e0} | Input e0: {trial_e0} | Output e0: {e0_2}")
                ú = Matrix(B,2,2,[á,b́,ć,d́])
                U2 = u2*Matrix(B,2,2,[1,α2,0,1])*ú
                if e0_2 == e0: break
            else:
                if verbose:
                    print("[Error] get_bde0: Could not achieve same value of e0.")
                continue
            e1_2 = ZZ(rn(U2)).log(L)
            if e1_2 != 2*e0:
                if verbose:
                    print(f"[Error] KLPT2: e1 ≠ 2*e0.\ne0 = {e0}\n𝒩(u2) = {factor(ZZ(rn(u2)))}\n𝒩(ú) = {factor(ZZ(rn(ú)))}")
                    breakpoint()
                continue
            if verbose:
                print("2E. Completed get_bde0.")
                print(f"b' = {b́}")
                print(f"d' = {d́}")
                print(f"e0' = {e0_2}")
                print(f"e1' = {e1_2}")
            if step_by_step: breakpoint()
                
            h1 = ct(U1) * g1 * U1
            h2 = ct(U2) * g2 * U2
            D = ZZ(h1[0][0])
            if D != ZZ(h2[0][0]):
                if verbose:
                    print(f"[Error] KLPT2: h1 and h2 do not have the same top left entry: {factor(D)} vs {factor(ZZ(h2[0][0]))}.")
                    breakpoint()
                continue
            if rn(h1) != rn(h2):
                if verbose:
                    print(f"[Error] KLPT2: h1 and h2 do not have the same reduced norm: {rn(h1)} vs {rn(h2)}.")
                    breakpoint()
                continue

            τ = Matrix(B,2,2,[D, h1[0][1]-h2[0][1], 0, D])
            γ = U2*τ*inv(U1)*rn(U1)
            e = 2*(e1_1+e2)
            if verbose:
                print(f"\nD = {D}")
                print(f"\ne = {e}")
            if ct(γ)*g2*γ != L^e * g1:
                print("[Error] KLPT2: Output is incorrect.")
                breakpoint()
                continue
            return γ, e

def get_acś(g, L=2, verbose=True):
    (s,r),(r̄,t) = g
    s,t = ZZ(s), ZZ(t)
    (r1, r2, r3, r4) = r.coefficient_tuple()
    Bgram  = Matrix(8,8,[     s,    0,    0,    0,  r1,  -r2,-p*r3,-p*r4,
                              0,    s,    0,    0,  r2,   r1,-p*r4, p*r3,
                              0,    0,  s*p,    0,p*r3, p*r4, p*r1,-p*r2,
                              0,    0,    0,  s*p,p*r4,-p*r3, p*r2, p*r1,
                             r1,   r2, p*r3, p*r4,   t,    0,    0,    0,
                            -r2,   r1, p*r4,-p*r3,   0,    t,    0,    0,
                          -p*r3,-p*r4, p*r1, p*r2,   0,    0,  t*p,    0,
                          -p*r4, p*r3,-p*r2, p*r1,   0,    0,    0,  t*p ])
    
    Q = Bgram.LLL_gram().transpose()
    A = [B(Q[i][0:4]) for i in range(4)]
    C = [B(Q[i][4:8]) for i in range(4)]
    
    def QuadraticForm_TopLeftEntry(a, c):
        return ZZ(s*rn(a) + t*rn(c) + tr(ct(c)*r̄*a))
    
    if verbose:
        print(f"[Debug] get_acś: 1st short vector gives s' = {QuadraticForm_TopLeftEntry(A[0],C[0])}.")
        print(f"[Debug] get_acś: 2nd short vector gives s' = {QuadraticForm_TopLeftEntry(A[1],C[1])}.")
        print(f"[Debug] get_acś: 3rd short vector gives s' = {QuadraticForm_TopLeftEntry(A[2],C[2])}.")
        print(f"[Debug] get_acś: 4th short vector gives s' = {QuadraticForm_TopLeftEntry(A[3],C[3])}.")
        print(f"[Debug] get_acś: Finding smallest prime s'.")
    
    min_ś_prime = Infinity
    min_ś_comp = Infinity
    count = 0
    terminate_threshold = 10^5
    m = 0
    while True:
        m += 1
        ind_range = [0] + [n for i in range(1,m+1) for n in [i,-i]]
        for ind in itertools.product(ind_range, repeat=int(4)):
            if all(abs(i) < m for i in ind): continue
            count += 1
            a = sum(ind[i]*A[i] for i in range(4))
            c = sum(ind[i]*C[i] for i in range(4))
            ś = ZZ(QuadraticForm_TopLeftEntry(a,c))
            if gcd(rn(a),rn(c)) == 1 and ś not in [1,2,L]:
                if ś.is_prime() and ś<min_ś_prime:
                    min_ś_prime = ś
                    min_a_prime = a
                    min_c_prime = c
                elif not ś.is_prime() and ś<min_ś_comp and not ś.is_power_of(L):
                    min_ś_comp = ś
                    min_a_comp = a
                    min_c_comp = c
            if (min_ś_prime == 3 and L != 3) or (min_ś_prime == 5 and L == 3) or (min_ś_prime < Infinity and count > terminate_threshold):
                return min_a_prime, min_c_prime, min_ś_prime
            if count > terminate_threshold*1.1 and min_ś_comp < Infinity and min_ś_prime == Infinity:
                return min_a_comp, min_c_comp, min_ś_comp
    raise Exception("[Error] get_acś: Can't find a suitable s'.")

def get_bde0(a,c,L=2,target_e0=100,verbose=True):
    try:
        ctx = KLPT_Context(B)
        I = O.left_ideal([rn(c), c*ct(a)])
        α, *_ = ctx.KLPT(I,T=L^target_e0, returnElem=True)
        Iα = O.left_ideal(α)
        e0 = ZZ(rn(α)/rn(c)).log(L)
        for _ in range(100):
            o1, o2 = get_o1o2(α, a, c)
            _, aa, cc = xgcd(rn(a), rn(c))
            b =  cc * (rn(c) * ct(o1) + a * ct(c) * ct(o2))
            d = -aa * (c * ct(a) * ct(o1) + rn(a) * ct(o2))
            e0́ = ZZ(rn(Matrix(B,2,2,[a,b,c,d]))).log(L)
            if e0 == e0́ : return b, d, e0
        return b, d, e0́
    except: # In the rare occurence where KLPT tries to reduce the ramified prime, which is unimplemented.
        return None, None, None

def get_o1o2(α,a,c):
    o2 = O.random_element()
    o1nc = α - o2 * c * ct(a)
    return o1nc / rn(c), o2

def get_αǵ(g, L=2, verbose=True):
    (s,r),(r̄,t) = g
    s,t = ZZ(s), ZZ(t)
    r_coords = change_basis(r)
    β = [ZZ(r_coords[i]).quo_rem(s) for i in range(4)]
    for tweak in itertools.product([True,False], repeat=int(4)):
        α = sum((β[i][0] + (1 if tweak[i] else 0)) * O.basis()[i] for i in range(4))
        ŕ = sum((β[i][1] - (s if tweak[i] else 0)) * O.basis()[i] for i in range(4))
        if ZZ(tr(ŕ)) % L != L-1:
            if ZZ(rn(ŕ)) % L == 0:
                α += 1
                ŕ -= s
            if ZZ(rn(ŕ)) % L == 0: continue
            α *= -1
            assert ŕ == r + α*s, "[Error] get_αǵ: α or r' was computed wrongly."
            t́ = ZZ(rn(α)*s+tr(ct(α)*r)+t)
            if t́ % s != 0:
                return α, Matrix(B,2,2,[s,ŕ,ct(ŕ),t́])
    print("[Debug] get_αǵ: Unable to find α satisfying all the conditions, probably because s is not prime.")
    α = -sum((β[i][0]) * O.basis()[i] for i in range(4))
    ŕ = sum((β[i][1]) * O.basis()[i] for i in range(4))
    t́ = ZZ(rn(α)*s+tr(ct(α)*r)+t)
    return α, Matrix(B,2,2,[s,ŕ,ct(ŕ),t́])

# def get_áće2(g, L=2, fixed_e2=None, min_e2=0, verbose=True):
#     (s,r),(r̄,t) = g
#     s,t = ZZ(s), ZZ(t)
#     assert s.is_prime(), f"[Error] get_áće2: Top left entry {s} is not prime."
#     K = GF(s)
#     e_bound = ZZ(rn(g)).log(L).n().floor()
#     e2_range = range(min_e2, e_bound) if fixed_e2 == None else [fixed_e2]
#     for e2 in e2_range:
#         for c2 in K:
#             c1_square = K(L^e2) / K(ZZ(t*p*rn(r))) - c2^2
#             if c1_square.is_square():
#                 c1 = sqrt(c1_square)
#                 c = ZZ(c1) * ct(r) * jj + ZZ(c2) * ct(r) * kk
#                 le_tnc = ZZ(L^e2 - t * rn(c))
#                 if le_tnc < 0: continue
#                 na, rem = ZZ(le_tnc).quo_rem(s)
#                 if rem != 0: continue
#                 try:
#                     a1,a2 = two_squares(na)
#                     return a1+a2*ii, c, e2
#                 except: continue
#     if verbose: print("[Error] get_áće2: Unable to find a' and c' in the allowed range of e2.")
#     return None, None, None

def get_áće2(g, L=2, fixed_e2=None, min_e2=0, verbose=True):
    (s,r),(r̄,t) = g
    s,t = ZZ(s), ZZ(t)
    K = Integers(s)
    invertible = False
    q = ZZ(t*p*rn(r))
    if K(q) != 0:
        if gcd(q,s) == 1:
            invertible = True
            q_inv = 1 / K(q)
        e_bound = ZZ(rn(g)).log(L).n().floor()
        if min_e2 == 0: min_e2 = t.log(2).n().ceil()
        e2_range = range(min_e2, e_bound) if fixed_e2 == None else [fixed_e2]
        for e2 in e2_range:
            for c2 in K:
                if c2 == 0: continue
                if invertible:
                    c1_square = K(ZZ(L^e2)) * q_inv - c2^2
                else:
                    for c1 in K:
                        if c1 == 0: continue
                        if K(q)*(c1^2+c2^2) == K(L^e2):
                            c1_square = c1^2
                            break
                    else:
                        continue
                if c1_square.is_square():
                    c1 = sqrt(c1_square)
                    c = ZZ(c1) * ct(r) * jj + ZZ(c2) * ct(r) * kk
                    le_tnc = ZZ(L^e2 - t * rn(c))
                    if le_tnc < 0: continue
                    na, rem = ZZ(le_tnc).quo_rem(s)
                    if rem != 0: continue
                    try:
                        a1,a2 = two_squares(na)
                        return a1+a2*ii, c, e2
                    except: continue
    if verbose: print("[Error] get_áće2: Unable to find a' and c' in the allowed range of e2.")
    return None, None, None


def example():
    g1 = random_polarisation_matrix()
    g2 = random_polarisation_matrix()
    print(g1)
    print(g2)
    γ,e = KLPT2(g1,g2,2,100) # Change the value of L and target_norm as required