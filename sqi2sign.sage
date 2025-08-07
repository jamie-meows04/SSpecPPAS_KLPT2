load('klpt2.sage')

A0 = ExE
BTB = BTB2_matrices()
kernels, Γ = get_all_ExE_kernels()

# Returns: [φ, γ, g] where:
# φ is a random isogeny from A0;
# γ is its matrix representation;
# g is the codomain of γ.
def random_isogeny_A0(length):
    M = identity_matrix(4)
    torsion = elliptic_product_torsion(A0, 2^length)
    φ = SSpecPPAS_Isogeny(None, A0, A0, lambda R : R)
    A = A0
    γ = I2
    K = [A0.infinity]
    for i in range(1,length+1):
        B = [2^(length-i) * P for P in torsion]
        while True:
            # Generate random isotropic (2,2)-kernel
            D = choices(BTB)[0]
            K = apply_BT_matrix(B, M*D)
            if not EE_Point.is_isotropic(K, 2^i) or not any(P.order() == 2^i for P in K): continue

            kerψ = EE_Point.span([φ(R) for R in K]) - {A.infinity}

            # Check if codomain is elliptic product
            # This condition can be removed once we speed up computation of gluing isogenies
            image_is_jacobian = not any(not R.P for R in kerψ)
            if image_is_jacobian:
                isomorphisms = A.E1.isomorphisms(A.E2)
                for α in isomorphisms:
                    if all(α(R[0])==R[1] for R in kerψ):
                        image_is_jacobian = False
                        break
            if image_is_jacobian: continue

            # Calculate the (2,2)-isogeny and its matrix
            ψ = A.kernel_22_to_codomain(kerψ, True)
            A = ψ.codomain
            φ = φ.compose(ψ)
            φ.kernel = K
            kerδ = evaluate_matrix_on_point(γ, K)
            kerδ_gens = make_linearly_independent(kerδ)
            kerδ = KernelData(gens=kerδ_gens)
            δ = Γ[kernels.index(kerδ)]
            γ = δ*γ
            M = M*D
            break
    return φ, γ, pm(γ,I2)

# Returns: φ, a random isogeny from A
def random_isogeny(A, length):
    assert not A.is_jacobian, "Proof of concept: This function is only implemented for elliptic products"
    M = identity_matrix(4)
    torsion = elliptic_product_torsion(A, 2^length) # TODO: generalise for Jacobians
    φ = SSpecPPAS_Isogeny(None, A, A, lambda R : R)
    K = [A.infinity]
    for i in range(1,length+1):
        B = [2^(length-i) * P for P in torsion]
        while True:
            # Generate random isotropic (2,2)-kernel
            D = choices(BTB)[0]
            K = apply_BT_matrix(B, M*D)
            if not EE_Point.is_isotropic(K, 2^i) or not any(P.order() == 2^i for P in K): continue

            kerψ = EE_Point.span([φ(R) for R in K]) - {A.infinity}

            # Check if codomain is elliptic product
            # This condition can be removed once we speed up computation of gluing isogenies
            image_is_jacobian = not any(not R.P for R in kerψ)
            if image_is_jacobian:
                isomorphisms = A.E1.isomorphisms(A.E2)
                for α in isomorphisms:
                    if all(α(R[0])==R[1] for R in kerψ):
                        image_is_jacobian = False
                        break
            if image_is_jacobian: continue

            # Calculate the (2,2)-isogeny
            ψ = A.kernel_22_to_codomain(kerψ, True)
            A = ψ.codomain
            φ = φ.compose(ψ)
            φ.kernel = K
            M = M*D
            break
    return φ

def adjoint_isogeny(φ, γ):
    return matrix_to_isogeny(φ, hn(γ)*inv(γ), φ.domain)

# Returns: γ, the matrix representation of φ
# ψ : A0 → domain(φ) ; γ=μ(ψ)
# The only instance when this is run is on g = gsk and φ = φchl
def isogeny_to_matrix(ψ, γ, φ):
    if ψ.codomain != A0: # Need to pull back kerφ to A0
        N = max(R.order() for R in φ.kernel)
        ψadj = adjoint_isogeny(ψ, γ)
        K = make_linearly_independent([ψadj(R) for R in φ.kernel]) # does not work...
    else:
        K = φ.kernel
    return kernel_to_matrix(K)

# Returns: φ : A → B, the standard representation of γ
# ψ : A0 → A
def matrix_to_isogeny(ψ, γ, B):
    N = hn(γ)
    γadj = N*inv(γ)
    torsion = elliptic_product_torsion(A0, N)
    K = evaluate_matrix_on_point(γadj, torsion)
    # Pushforward K under ψ to A
    K = make_linearly_independent([ψ(R) for R in K])
    breakpoint()
    ψ = kernel_to_isogeny(K)
    C = ψ.codomain
    α = C.E1.isomorphism_to(B.E1)
    β = C.E2.isomorphism_to(B.E2)
    θ = SSpecPPAS_Isogeny(None, C, B, lambda R : EE_Point(α(R.P), β(R.Q)))
    φ = ψ.compose(θ)
    φ.kernel = ψ.kernel
    return φ

def kernel_to_matrix(K):
    K.sort(key = lambda R : -R.order())
    orders = [R.order() for R in K]
    assert orders[0] == prod(orders[1:]), "Kernel must be specified by linearly independent generators."
    γ_ = I2
    if len(K) == 3:
        K_ = [K[0] * orders[2], K[1]]
        γ_ = rank_2_kernel_to_matrix(K_)
        K = [R for R in evaluate_matrix_on_point(γ_, K) if R != A0.infinity]
    γ = rank_2_kernel_to_matrix(K)
    return γ*γ_

def rank_2_kernel_to_matrix(K):
    n = K[0].order().log(2)
    γ = I2
    for i in range(1,n+1):
        K_ = KernelData(gens = [2^(n-i) * R for R in K])
        δ = Γ[kernels.index(K_)]
        γ = δ * γ
        K = evaluate_matrix_on_point(δ, K)
    return γ

def kernel_to_isogeny(K):
    K.sort(key = lambda R : -R.order())
    orders = [R.order() for R in K]
    assert orders[0] == prod(orders[1:]), "Kernel must be specified by linearly independent generators."
    A = SSpecPPAS([K[0].P.curve(), K[0].Q.curve()])
    φ_ = SSpecPPAS_Isogeny(None, A, A, lambda R : R)
    if len(K) == 3:
        K_ = [K[0] * orders[2], K[1]]
        φ_ = rank_2_kernel_to_isogeny(K_)
        K = [φ_(R) for R in K if R != φ_.codomain.infinity]
    φ = rank_2_kernel_to_isogeny(K)
    φ = φ_.compose(φ)
    φ.kernel = K
    return φ

def rank_2_kernel_to_isogeny(K):
    n = K[0].order().log(2)
    A = SSpecPPAS([K[0].P.curve(), K[0].Q.curve()])
    φ = SSpecPPAS_Isogeny(None, A, A, lambda R : R)
    for i in range(1,n+1):
        K_ = EE_Point.span([2^(n-i) * R for R in K]) - {A.infinity}
        ψ = A.kernel_22_to_codomain(K_, True)
        A = ψ.codomain
        φ = φ.compose(ψ)
        K = [ψ(R) for R in K]
    return φ

def sqi2sign():
    # Key generation
    φsk, γsk, gsk = random_isogeny_A0(2)
    Apk = φsk.codomain

    # Commitment
    φcom, γcom, gcom = random_isogeny_A0(2)
    Acom = φcom.codomain

    # Challenge
    φchl = random_isogeny(Apk, 2)
    Achl = φchl.codomain
    
    # Response
    γchl = isogeny_to_matrix(φsk, γsk, φchl)
    gchl = pm(γchl, γsk)
    γrsp = KLPT2(gcom, gchl, 2, 100, False)
    φrsp = matrix_to_isogeny(φcom, γrsp, Achl)

    # Verification
    assert φrsp.domain == Acom and φrsp.codomain == Achl