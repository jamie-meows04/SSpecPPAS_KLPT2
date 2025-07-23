# Define the prime p before loading this file. Default: 2591.

from collections import *
import itertools
from random import *
import matplotlib.pyplot as plt
from sage.schemes.hyperelliptic_curves.invariants import absolute_igusa_invariants_kohel

if 'jacobian_generators_dict' not in globals() or jacobian_generators_dict == None:
    jacobian_generators_dict = dict()

class SSpecPPAS:
    def __init__(self, obj):
        dummy_f = x^6+1
        dummy_C = HyperellipticCurve(dummy_f)
        dummy_J = dummy_C.jacobian()
        dummy_E = EllipticCurve(F,j=1728)
        if isinstance(obj, type(dummy_f)):
            obj = HyperellipticCurve(obj)
        if isinstance(obj, type(dummy_C)):
            obj = obj.jacobian()
        if isinstance(obj, type(dummy_J)):
            self.is_jacobian = True
            self.surface = self.J = obj
            self.curve = self.C = obj.curve()
            self.field = self.curve.base()
            self.poly = self.curve.hyperelliptic_polynomials()[0]
            self.infinity = self.curve(0,1,0)

            self.field_ext, self.extension_map = self.field.extension(2,'ζ', map=True)
            self.inv_ext_map = self.extension_map.section()
            self.poly_ext = self.poly.change_ring(self.field_ext)
            self.poly_roots = self.poly_ext.roots(multiplicities=False)
            self.curve_ext = self.curve.change_ring(self.field_ext)
            self.jacobian_ext = self.curve_ext.jacobian()
            self.infinity_ext = self.curve_ext(0,1,0)

            self.weierstrass_points = [self.curve_ext((r,0)) for r in self.poly_roots]
            if len(self.weierstrass_points) == 5: self.weierstrass_points.append(self.infinity_ext)
            assert len(self.weierstrass_points) == 6
            
            self.invariant = absolute_igusa_invariants_kohel(self.poly)
            self.cardinality = self.curve.frobenius_polynomial()(1)
            self.gens = None
            # Get type
            A,B,C,D = self.C.clebsch_invariants()
            A11 = 2*C+A*B/3
            A12 = 2*(B^2+A*C)/3
            A23 = B/2*A12+C/3*A11
            A22 = A31 = D
            A33 = B/2*A22+C/3*A12
            R = matrix(3,3,[A11,A12,A31,A12,A22,A23,A31,A23,A33]).determinant()
            if R!=0 and (A,B,C)!=(0,0,0):
                self.type=0
            elif (A,B,C)==(0,0,0) or self.invariant == absolute_igusa_invariants_kohel(x^5-1):
                self.type=2
            elif B*A11-2*A*A12==-6*D and C*A11+2*B*A12==A*D and 6*C^2!=B^3 and D!=0:
                self.type=3
            elif 6*C^2==B^3 and 3*D==2*B*A11 and 2*A*B!=15*C and D!=0:
                self.type=4
            elif 6*B==A^2 and D==0 and A11==0 and A!=0:
                self.type=5
            elif (A!=0 and (B,C,D)==(0,0,0)) or self.invariant == absolute_igusa_invariants_kohel(x^5+x):
                self.type=6
            elif R==0:
                self.type=1
            else: self.type=None # Unknown
            if self.type==None:
                print(R==0)
                print(A11*A22)
                print(A12)
        if isinstance(obj, type(dummy_E)):
            obj = (obj, obj)
        if type(obj) in [set, tuple, list] and len(obj)==2:
            self.is_jacobian = False
            self.surface = tuple(obj)
            self.curve = None
            self.E1, self.E2 = self.surface
            self.field = self.E1.base()
            self.infinity = EE_Point(obj[0](0), obj[1](0))
            self.invariant = tuple(sorted([self.E1.j_invariant(), self.E2.j_invariant()]))
            self.cardinality = self.E1.count_points() * self.E2.count_points()
            self.gens = [EE_Point(self.E1.gens()[0], self.E2(0)), EE_Point(self.E1.gens()[1], self.E2(0)), EE_Point(self.E1(0), self.E2.gens()[0]), EE_Point(self.E1(0), self.E2.gens()[1])]

            # Get type
            self.j1, self.j2 = [E.j_invariant() for E in obj]
            J = {self.j1,self.j2}
            j = 1728 % p
            S = {0,j}.intersection(J)
            if len(J)==2:
                if not S:
                    self.type=-1
                elif S == {0}:
                    self.type=-2
                elif S == {j}:
                    self.type=-3
                elif S == {0,j}:
                    self.type=-4
                else: raise ValueError()
            else:
                if not S:
                    self.type=-5
                elif S == {0}:
                    self.type=-6
                elif S == {j}:
                    self.type=-7
                else: raise ValueError()
            
            # Get 2-torsion subgroups
            TB1 = self.E1.torsion_basis(2)
            self.torsion1 = [α*TB1[0]+β*TB1[1] for β in range(2) for α in range(2)]
            TB2 = self.E2.torsion_basis(2)
            self.torsion2 = [α*TB2[0]+β*TB2[1] for β in range(2) for α in range(2)]
        
        if self.is_jacobian==None: raise TypeError(f"Type of input 'obj' is incompatible.")
        assert self.is_superspecial()

        self.kernels = [self.get_kernel(i,True) for i in range(15)]

    def __repr__(self):
        return self.surface.__repr__()

    def is_superspecial(self):
        if not self.is_jacobian: return self.E1.is_supersingular() and self.E2.is_supersingular()
        if self.curve.degree() == 5: return self.curve.Hasse_Witt()==0
        g = self.poly^((p-1)/2)
        return all([g[p*i-j]==0 for i in range(1,3) for j in range(1,3)])
    
    def mumford_to_quad_split(self, D):
        cr = self.lc().nth_root(3)
        quad_split = [cr*D[i][0] for i in range(3)]
        assert product(quad_split) == self.poly
        return quad_split
    
    def quad_split_to_mumford(self, quad_split):
        mumfords = []
        for fi in quad_split:
            roots = fi.change_ring(self.field_ext).roots(multiplicities=False)
            x = self.field_ext['x'].0
            mumfords.append(self.jacobian_ext(product(x-r for r in roots), 0))
        return mumfords
    
    indices_dict = { 0: [(0,1),(2,3),(4,5)],
                     1: [(0,1),(2,4),(3,5)],
                     2: [(0,1),(2,5),(3,4)],
                     3: [(0,2),(1,3),(4,5)],
                     4: [(0,2),(1,4),(3,5)],
                     5: [(0,2),(1,5),(3,4)],
                     6: [(0,3),(1,2),(4,5)],
                     7: [(0,3),(1,4),(2,5)],
                     8: [(0,3),(1,5),(2,4)],
                     9: [(0,4),(1,2),(3,5)],
                    10: [(0,4),(1,3),(2,5)],
                    11: [(0,4),(1,5),(2,3)],
                    12: [(0,5),(1,2),(3,4)],
                    13: [(0,5),(1,3),(2,4)],
                    14: [(0,5),(1,4),(2,3)] }

    def get_kernel(self, indices, full=False): # always isotropic
        if type(indices) in [int, Integer]:
            try: return self.kernels[indices][0] if not full else self.kernels[indices]
            except: pass
        if not self.is_jacobian:
            if type(indices) not in [int, Integer]: raise TypeError(f"'indices' must be an integer")
            if indices<9:
                i,j,k = indices//3+1, indices%3+1, None
                ker = [EE_Point(self.torsion1[i],self.torsion2[0]), EE_Point(self.torsion1[0],self.torsion2[j])]
                image_is_jacobian = False
            else:
                i,j,k = list(itertools.permutations([1,2,3]))[indices-9]
                ker = [EE_Point(self.torsion1[1],self.torsion2[i]), EE_Point(self.torsion1[2],self.torsion2[j])]
                image_is_jacobian = True
                if self.type<-4: 
                    isomorphisms = self.E1.isomorphisms(self.E2)
                    for ψ in isomorphisms:
                        if ψ(self.torsion1[1])==self.torsion2[i] and ψ(self.torsion1[2])==self.torsion2[j] and ψ(self.torsion1[3])==self.torsion2[k]:
                            image_is_jacobian = False
                            break
            assert ker[0].weil_pairing(ker[1], 2) == 1
            kernel = ker + [ker[0]+ker[1], ker[0]*0]
            kernel = KernelData(self.id_of_2_torsion_points(kernel), ker, kernel)
            return kernel, image_is_jacobian, (0,i,j,k)

        if hasattr(indices,'__iter__') and len(indices) not in [3,6]:
            raise ValueError(f"Length of 'indices' must be 3 or 6.")
        elif type(indices) in [int, Integer]:
            indices = SSpecPPAS.indices_dict[indices]
        elif len(indices) == 6:
            indices = list(zip(indices[::2],indices[1::2]))
        _.<x> = self.field_ext[]
        semi_quad_split = [product([(x-self.poly_roots[j]) for j in i if j<len(self.poly_roots)]) for i in indices]
        kernel = self.quad_split_to_mumford(semi_quad_split) + [self.J(0)]
        kernel = KernelData(str(indices), kernel[:2], kernel)
        return kernel, semi_quad_split
    
    def kernel_to_isogeny(self, indices, compute_maps=False):
        if not self.is_jacobian:
            kernel, image_is_jacobian, π = self.get_kernel(indices,True)
            if not image_is_jacobian:
                isogeny = EE_Point.isogeny_EE(kernel.gens)
                φ = SSpecPPAS_Isogeny(kernel, self, SSpecPPAS(isogeny.codomain), isogeny if compute_maps else None)
            else:
                _.<x> = self.field[]
                α = [self.torsion1[i][0] for i in range(4)]
                β = [self.torsion2[π[i]][0] for i in range(4)]
                a1 = (α[3]-α[2])^2/(β[3]-β[2]) + (α[2]-α[1])^2/(β[2]-β[1]) + (α[1]-α[3])^2/(β[1]-β[3])
                b1 = (β[3]-β[2])^2/(α[3]-α[2]) + (β[2]-β[1])^2/(α[2]-α[1]) + (β[1]-β[3])^2/(α[1]-α[3])
                a2 = α[1]*(β[3]-β[2]) + α[2]*(β[1]-β[3]) + α[3]*(β[2]-β[1])
                b2 = β[1]*(α[3]-α[2]) + β[2]*(α[1]-α[3]) + β[3]*(α[2]-α[1])
                A = (β[2]-β[3])^2 * (β[1]-β[3])^2 * (β[1]-β[2])^2 * a1/a2
                B = (α[2]-α[3])^2 * (α[1]-α[3])^2 * (α[1]-α[2])^2 * b1/b2
                g1 = A*(α[2]-α[1])*(α[1]-α[3])*x^2 + B*(β[2]-β[1])*(β[1]-β[3])
                g2 = A*(α[3]-α[2])*(α[2]-α[1])*x^2 + B*(β[3]-β[2])*(β[2]-β[1])
                g3 = -(A*(α[1]-α[3])*(α[3]-α[2])*x^2 + B*(β[1]-β[3])*(β[3]-β[2]))
                J = SSpecPPAS(g1*g2*g3)
                if compute_maps:
                    gens = J.get_jacobian_generators()
                    G1 = self.E1.gens()
                    G2 = self.E2.gens()
                    ker_coefficients = [kernel[i].P.log(self.E1.gens())+kernel[i].Q.log(self.E2.gens()) for i in range(4)]
                    def φ(R):
                        J_ = J
                        coefficients = R.P.log(self.E1.gens())+R.Q.log(self.E2.gens())
                        set_coefficients = [[coefficients[i]-K[i] for i in range(4)] for K in ker_coefficients]
                        sizes = [sum(c^2 for c in C) for C in set_coefficients]
                        min_size = min(sizes)
                        index = sizes.index(min_size)
                        representative = set_coefficients[index]
                        divisor = sum(gens[i]*representative[i] for i in range(4))
                        return divisor
                    φ = SSpecPPAS_Isogeny(kernel, self, J, φ)
                else: φ = SSpecPPAS_Isogeny(kernel, self, J, None)
            return φ
        
        _.<x> = self.field_ext[]
        kernel, (f0_,f1_,f2_) = self.get_kernel(indices,True)
        first_try = True
        while True:
            if first_try:
                roots = self.poly_ext.lc().nth_root(3,all=True)
                if not roots:
                    first_try = False
                    continue
                α = β = roots[0]
            else:
                α, β = self.field.random_element(), self.field.random_element()
                if α==0 or β==0: continue
            γ = self.poly.lc()/(α*β)
            f0 = f0_*α
            f1 = f1_*β
            f2 = f2_*γ
            quad_split = f0,f1,f2
            if f0*f1*f2 != self.poly:
                first_try = False
                continue
            M = matrix(3,3,[quad_split[j][i] for i in range(3) for j in range(3)])
            δ = M.determinant()
            if δ!=0:
                g0,g1,g2 = [δ^(-1)*(quad_split[(i+1)%3].derivative()*quad_split[(i+2)%3]-quad_split[(i+2)%3].derivative()*quad_split[(i+1)%3]) for i in range(3)]
                g = g0*g1*g2
                x = self.field['x'].0
                g = sum(x^i * self.inv_ext_map(g[i]) for i in range(g.degree()+1))
                C1 = HyperellipticCurve(g)
                J1 = C1.jacobian()
                Fp8 = self.field_ext.extension(2)
                C2 = C1.base_extend(Fp8)
                J2 = C2.jacobian()
                def φ(D):
                    if D in kernel.points: return J1(0)
                    points = self.divisor_to_supports(D)
                    images = [None,None] # points on the image curve
                    for i in range(len(points)):
                        if points[i] == self.infinity:
                            images[i] = 0
                            continue
                        assert points[i][2] == 1
                        u,v = points[i][:2]
                        poly = f0(u)*g0+f1(u)*g1
                        roots = poly.change_ring(Fp8).roots()
                        multiplicity = roots[0][1]
                        x1 = roots[0][0]
                        x2 = roots[1][0] if multiplicity == 1 else x1
                        if v==0: y1,y2=(0,0)
                        elif multiplicity == 1:
                            y1,y2 = [f0(u)*g0(r)*(u-r)/v for r in [x1,x2]]
                        else:
                            α,β,γ = y1 = C2.lift_x(x1)
                            y2 = C2(α,-β,γ)
                        images[i] = [C2(x1,y1), C2(x2,y2)]
                    image_extended = sum(J2(images[i][0]) + J2(images[i][1]) for i in range(len(points)))
                    u = image_extended[0].change_ring(self.field)
                    v = image_extended[1].change_ring(self.field)
                    return J1(u,v)
                return SSpecPPAS_Isogeny(kernel, self, SSpecPPAS(J1), φ if compute_maps else None)
            D = (f0[1]+x*f1[1])^2-4*(f0[0]+x*f1[0])*(f0[2]+x*f1[2])
            λ1,λ2 = D.roots(multiplicities=False)
            U2,V2 = f0+λ1*f1, f0+λ2*f1
            if not (U2.is_square() and V2.is_square()):
                first_try = False
                continue
            α0,β0,α1,β1 = λ2/(λ2-λ1), λ1/(λ1-λ2), 1/(λ1-λ2), 1/(λ2-λ1)
            M_ = M[:,0:2]
            v = M[:,-1]
            z1,z2=M_.solve_right(v)
            z1,z2 = z1[0],z2[0]
            assert z1*f0 + z2*f1 == f2, "Matrix solution is incorrect."
            α2,β2 = z1*α0+z2*α1, z1*β0+z2*β1
            assert f0 == α0*U2+β0*V2 and f1 == α1*U2+β1*V2 and f2 == α2*U2+β2*V2
            α,β = [α0,α1,α2], [β0,β1,β2]
            _.<X,Y,Z> = self.field_ext[]
            ψ1 = EllipticCurve_from_cubic(Y^2*Z-product([α[i]*X+β[i]*Z for i in range(3)]), [0,1,0])
            ψ2 = EllipticCurve_from_cubic(Y^2*Z-product([β[i]*X+α[i]*Z for i in range(3)]), [0,1,0])
            C1,C2 = ψ1.domain(), ψ2.domain()
            E1_,E2_ = ψ1.codomain(), ψ2.codomain()
            E1 = E1_.change_ring(self.field)
            E2 = E2_.change_ring(self.field)
            codomain = SSpecPPAS([E1,E2])
            U,V=sqrt(U2),sqrt(V2)
            def φ(D):
                points = self.divisor_to_supports(D)
                if len(points)==1: points.append(self.infinity)
                p1,p2,p3 = points[0]
                q1,q2,q3 = (U2(p1)/V2(p1),p2/(V(p1)^3),1) if points[0][1]!=0 and points[0][:]!=(0,1,0) else (0,1,0)
                P1 = ψ1([q1,q2,q3])
                p1,p2,p3 = points[1]
                q1,q2,q3 = (U2(p1)/V2(p1),p2/(V(p1)^3),1) if points[0][1]!=0 and points[0][:]!=(0,1,0) else (0,1,0)
                Q1 = ψ1([q1,q2,q3])
                
                p1,p2,p3 = points[0]
                q1,q2,q3 = (V2(p1)/U2(p1),p2/(U(p1)^3),1) if points[1][1]!=0 and points[1][:]!=(0,1,0) else (0,1,0)
                P2 = ψ2([q1,q2,q3])
                p1,p2,p3 = points[1]
                q1,q2,q3 = (V2(p1)/U2(p1),p2/(U(p1)^3),1) if points[1][1]!=0 and points[1][:]!=(0,1,0) else (0,1,0)
                Q2 = ψ2([q1,q2,q3])

                image1 = EE_Point(P1,P2)
                image2 = EE_Point(Q1,Q2)
                image_ext = image1 + image2
                image = EE_Point(image_ext.P.change_ring(self.field), image_ext.Q.change_ring(self.field))
                return image
            return SSpecPPAS_Isogeny(kernel, self, codomain, φ if compute_maps else None)
    
    # Returns the supports of the divisor, over the splitting field if extension is True, otherwise over the base field
    def divisor_to_supports(self, divisor, extension=True):
        if not self.is_jacobian: raise TypeError(f"This method is only implemented for Jacobians.")
        if hasattr(divisor, 'len') and len(divisor)==3: return [divisor]
        if divisor == self.J(0): return [self.infinity_ext]
        u,v = divisor
        C = self.curve
        if extension:
            u = u.change_ring(self.field_ext)
            v = v.change_ring(self.field_ext)
            C = self.curve_ext
        roots = u.roots(multiplicities=False)
        ys = [v(r) for r in roots]
        return [C(roots[i],ys[i]) for i in range(len(roots))]
    
    def negate_curve_point(self, P):
        if self.is_jacobian and len(P)==3: return self.curve([P[0],-P[1],P[2]])
        if type(P) == EE_Point: return P*(-1)
        raise TypeError(f"The input 'P' should be a projective point on the hyperelliptic curve or an EE_Point.")
    
    def lift_x(self, x=None, jacobian=True, negate=False):
        if not self.is_jacobian: raise TypeError(f"This method is only implemented for Jacobians.")
        if x==None: return self.infinity if not jacobian else self.J(0)
        P = self.C.lift_x(self.field(x))
        Q = P if not negate else self.negate_curve_point(P)
        return self.J(Q) if jacobian else Q
    
    def __repr__(self):
        return self.surface.__repr__()

    def get_jacobian_generators(self):
        if not self.is_jacobian: raise TypeError(f"This method is only implemented for Jacobians.")
        if self.gens != None and len(self.gens)==4: return self.gens
        if self.poly in jacobian_generators_dict: return jacobian_generators_dict[self.poly]
        gens = []
        gen_order = self.cardinality.nth_root(4)
        gen_subgroup = [self.J(0)]
        while len(gens)<4:
            α,β = choices(self.curve.points(), k=int(2))
            test = self.J(α)+self.J(β)
            if test in gen_subgroup or (test*(gen_order//2)).is_zero(): continue # assumes 2 | gen_order
            gens.append(test)
            if len(gens)<4:
                test_multiples = [q*test for q in range(1,gen_order)]
                gen_subgroup += [test_mul+d for test_mul in test_multiples for d in gen_subgroup]
        self.gens = jacobian_generators_dict[self.poly] = gens
        assert len(gen_subgroup)*gen_order == self.cardinality
        return gens

    def __getitem__(self, item):
        if not self.is_jacobian: return self.E1 if item==0 else self.E2
        return self.J(item)

    def id_of_2_torsion_points(self, points):
        if self.is_jacobian: raise TypeError(f"This method is only implemented for elliptic products.")
        if type(points) not in [tuple, set, list]: points = [points]
        output = []
        for point in points:
            i,j = self.torsion1.index(point.P), self.torsion2.index(point.Q)
            i,j = "OQRP"[i], "OQRP"[j]
            output.append(f"{i}{j}")
        return output

class SSpecPPAS_Isogeny:
    def __init__(self, kernel, domain, codomain, map):
        self.kernel = kernel
        self.domain = domain
        self.codomain = codomain
        self.map = map
    def __call__(self, args):
        return self.map(args)
    def __repr__(self):
        return f"Isogeny from {self.domain} to {self.codomain}"
    def compose(self, other):
        return SSpecPPAS_Isogeny(None, self.domain, other.codomain, lambda R : other.map(self.map(R)))
    def power(self, n):
        assert self.domain == self.codomain and len(self.kernel)==1, "Taking powers is only implemented for automorphisms."
        α = SSpecPPAS_Isogeny([self.domain.infinity], self.domain, self.domain, lambda R : R)
        if n == 0: return α
        for i in range(n):
            α = α.compose(self)
        return α

class EE_Point:
    def __init__(self, P, Q):
        self.P = P
        self.Q = Q
        self.E1 = P.curve()
        self.E2 = Q.curve()
    
    def __add__(self, R):
        return EE_Point(self.P+R.P, self.Q+R.Q)
    
    def __sub__(self, R):
        return EE_Point(self.P-R.P, self.Q-R.Q)
    
    def __neg__(self):
        return (-1)*self
    
    def __mul__(self, m):
        return EE_Point(m*self.P, m*self.Q)
    
    def __rmul__(self, m):
        return EE_Point(m*self.P, m*self.Q)

    def __str__(self):
        return f"({self.P}, {self.Q})"

    def __repr__(self):
        return f"({self.P}, {self.Q})"
        
    def __eq__(self, other):
        return self.P == other.P and self.Q == other.Q
        
    def __ne__(self, other):
        return not self.__eq__(other)
    
    def __hash__(self):
        return hash((self.P, self.Q))

    def order(self):
        return lcm(self.P.order(), self.Q.order())
    
    def weil_pairing(self, other, N=2):
        return self.P.weil_pairing(other.P,N) * self.Q.weil_pairing(other.Q,N)
    
    def is_isotropic(gens, N=2):
        return all(g1.weil_pairing(g2, N) == 1 for g1,g2 in itertools.combinations(gens, r=int(2)))

    def isogeny_EE(P, Q = None):
        if hasattr(P,'__iter__') and len(P)==2:
            P,Q = P[0], P[1]
        E1 = P.P.curve()
        E2 = P.Q.curve()
        assert E1 == Q.P.curve() and E2 == Q.Q.curve()
        φ1 = E1.isogeny([P.P, Q.P])
        φ2 = E2.isogeny([P.Q, Q.Q])
        φ = lambda R : tuple([EE_Point(φ1(S.P),φ2(S.Q)) for S in R]) if hasattr(R,'__iter__') else EE_Point(φ1(R.P),φ2(R.Q))
        φ.φ1, φ.φ2 = φ1, φ2
        φ.codomain = (φ1.codomain(), φ2.codomain())
        φ.ker_gens = [P,Q]
        return φ

    def __getitem__(self, item):
        if item not in [0,1]: raise ValueError()
        return self.P if item==0 else self.Q
    
    def sum(points):
        points = list(points)
        if len(points) == 0: return ExE.infinity
        output = points[0]
        for i in range(1,len(points)):
            output += points[i]
        return output
    
    def span(points):
        if isinstance(points, EE_Point): points = [points]
        if len(points) == 0: return [ExE.infinity]
        points = list(points)
        return set([EE_Point.sum(α[i]*points[i] for i in range(len(points))) for α in itertools.product(*[range(P.order()) for P in points])])
    
    def log(self, basis): # basis is of the form generated by ExE_torsion
        assert len(basis) == 4
        assert not basis[0].Q and not basis[1].P and basis[0].P == basis[1].Q
        assert not basis[2].Q and not basis[3].P and basis[2].P == basis[3].Q
        a,c = self.P.log([basis[0].P, basis[2].P])
        b,d = self.Q.log([basis[1].Q, basis[3].Q])
        return a,b,c,d
    
class KernelData:
    def __init__(self, id=None, gens=None, points=None):
        if gens == None: raise ValueError("gens cannot be None")
        self.gens = gens
        self.points = points if points != None else EE_Point.span(gens)
        self.id = id if id != None else ExE.id_of_2_torsion_points(self.points)
        self.is_isotropic = EE_Point.is_isotropic(gens, max(R.order() for R in gens))

    def __repr__(self):
        return self.id.__repr__()

    def __str__(self):
        return self.id.__repr__()

    def __getitem__(self, item):
        return self.points[item]

    def __contains__(self, item):
        return item in self.points
    
    def __iter__(self):
        yield from self.points
    
    def __eq__(self, other):
        return set(self.points) == set(other.points)

def walk(vertex, root, point):
    surfaces = [root]
    isogenies = []
    points = [point]
    while len(surfaces) <= len(vertex):
        φ = surfaces[-1].kernel_to_isogeny(vertex[len(surfaces)-1],True)
        point = φ.map(point)
        surfaces.append(φ.codomain)
        isogenies.append(φ.map)
        points.append(point)
    return surfaces, isogenies, points

def neighbours(A, print_types=True, compute_maps=False):
    isogenies = [A.kernel_to_isogeny(i,compute_maps) for i in range(15)]
    if print_types: print([φ.codomain.type for φ in isogenies])
    return isogenies

def neighbours_polarisations(g, check_pm=False, pretty_print=False):
    output = [pm(γ,g) for γ in matrices]
    if not check_pm:
        if pretty_print:
            for i, neighbour in enumerate(output):
                print(f"{i}:\t{list(neighbour)}")
    else:
        output = [(pm(g),g) for g in output]
        if pretty_print:
            for i, (is_valid, neighbour) in enumerate(output):
                print(f"{i}:\t{is_valid}\t{list(neighbour)}")
    return output

def iota(P):
    E = P.curve()
    if P == E(0): return P
    z = P.base_ring().gen()
    (x,y) = P.xy()
    return E([-x,z*y])
    
def frob(P): return P.curve().frobenius_isogeny()(P)

def evaluate_endomorphism(alpha,P):
    if alpha == 1 or P.is_zero():
        return P
    elif alpha == -1:
        return -P
    elif alpha == 0:
        return P.curve()(0)
    coeff = alpha.coefficient_tuple()
    d = alpha.denominator()
    Qlist = P.division_points(d)
    retlist = []
    for Q in Qlist:
        Q1 = d * coeff[0] * Q
        Q2 = d * coeff[1] * iota(Q)
        Q3 = d * coeff[2] * frob(Q)
        Q4 = d * coeff[3] * iota(frob(Q))
        retlist.append(Q1 + Q2 + Q3 + Q4)
    retset = set(retlist)
    if len(retset) != 1: print(f"Warning: {len(retset)} possible outputs for ({alpha})({P})")
    return retlist[0]

def evaluate_matrix_on_point(M, X):
    if hasattr(X, 'weil_pairing'):
        return EE_Point(evaluate_endomorphism(M[0][0], X[0]) + evaluate_endomorphism(M[0][1], X[1]), evaluate_endomorphism(M[1][0], X[0]) + evaluate_endomorphism(M[1][1], X[1]))
    if hasattr(X, 'gens'): # KernelData
        return [evaluate_matrix_on_point(M,x) for x in X.gens]
    if hasattr(X, '__iter__'): # tuple, set, list
        return [evaluate_matrix_on_point(M,x) for x in X]
    raise TypeError()

def matrix_has_kernel(M, K):
    return all(R == ExE.infinity for R in evaluate_matrix_on_point(M,K))

# Express a quaternion element as a linear combination of the basis elements of O
def change_basis(x):
    if type(x)==sage.matrix.matrix_generic_dense.Matrix_generic_dense:
        return [change_basis(y) for row in x for y in row]
    OBasisMatrix = Matrix(QQ,4,4,[i for sub in O.basis() for i in sub]).transpose()
    Oinv = OBasisMatrix.inverse()
    return Oinv*vector(QQ,x.coefficient_tuple())

def compute_table_2_torsion(E0):
    E0TwoTors = E0(0).division_points(2)
    for a in O.basis():
        print(a)
        for P in E0TwoTors:
            print(P, "↦", evaluate_endomorphism(a,P))

# Finds the matrices encoding (l,l)-isogenies with the specified kernel generators `ker`
# `ker` can also be the index of the isotropic kernel encoding a Richelot isogeny.
# Set `single` to return only one matrix representing that kernel.
# The search space for these matrices' entries' coefficient tuples is `coefficients_space`.
# Set `target_norm` to 0 to return all matrices with non-zero reduced norm.
def find_kernel_matrices(ker_gens, single=True, coefficients_space=[0,1,-1], target_norm=4):
    ii,jj,kk = B.gens()

    # Load cache if available
    H = hash(tuple(ker_gens) + tuple(sorted(coefficients_space)) + (target_norm,))
    try:
        load(f"cache/kernel_matrices_{H}.sage")
        for M in globals()[f"_matrices_temp"]: M.set_immutable()
        return globals()[f"_matrices_temp"]
    except: pass

    possible_rows = possible_rows_dict[H] if possible_rows_dict != None and H in possible_rows_dict else []

    if not single:
        # Obtain possible rows of the matrix
        if not possible_rows:
            count, total_count = 0, len(coefficients_space)^8
            for coeffs in itertools.product(coefficients_space,repeat=8):
                if count%10 == 0: print(f"{H}: {count} of {total_count} rows", end='\t\r')
                count += 1
                if not any(coeffs): continue
                α = sum(coeffs[i] * O.basis()[i] for i in range(4))
                β = sum(coeffs[i+4] * O.basis()[i] for i in range(4))
                # Check if the row sends kernel to ∞
                if any([evaluate_endomorphism(α,R.P) + evaluate_endomorphism(β,R.Q) != 0 for R in ker_gens]):
                    continue
                possible_rows.append(([α,β],coeffs))
            possible_rows_dict[H] = possible_rows
            print(f"{index}: {len(possible_rows)} possible rows found")
        
        # Construct matrices with reduced norm
        matrices_and_sizes = []
        count, total_count = 0, len(possible_rows)*(len(possible_rows)-1)/2
        for U,V in itertools.combinations(possible_rows,r=int(2)):
            if count%10 == 0: print(f"{index}: {count} of {total_count} matrices", end='\t\r')
            count += 1
            M = Matrix(B,2,2,[U[0],V[0]])
            M.set_immutable()
            if (rn(M) == target_norm if target_norm else rn(M)>0):
                size = sum(abs(α) for α in U[1]+V[1])
                M_ = M[::-1]
                M_.set_immutable()
                matrices_and_sizes.append((M,size))
                matrices_and_sizes.append((M_,size))
        print(f"{index}: {len(matrices_and_sizes)} matrices found")
        
        # Sort by the complexity
        matrices_and_sizes.sort(key = lambda M : M[1])
        matrices = [M[0] for M in matrices_and_sizes]

        # Cache matrices
        with open(f"cache/kernel_matrices_{H}.sage", 'w') as file:
            file.write(f'globals()["_matrices_temp"] = [')
            for M in matrices:
                file.write(f"Matrix(B,2,2,{list(M)}),")
            file.write("]")
        
        if not matrices:
            print(f"find_kernel_matrices could not find any suitable matrices from {len(possible_rows)} possible rows with coefficients in {coefficients_space}.")
            print(f"Access the possible rows from possible_rows_dict[{H}].")
        return matrices
    else:
        if not possible_rows:
            # Obtain possible rows of the matrix
            count, total_count = 0, len(coefficients_space)^8
            for coeffs in itertools.product(coefficients_space,repeat=8):
                if count%10 == 0: print(f"{H}: {count} of {total_count} rows", end='\t\r')
                count += 1
                if not any(coeffs): continue
                α = sum(coeffs[i] * O.basis()[i] for i in range(4))
                β = sum(coeffs[i+4] * O.basis()[i] for i in range(4))
                # Check if the row sends kernel to ∞
                if any([evaluate_endomorphism(α,R.P) + evaluate_endomorphism(β,R.Q) != 0 for R in ker_gens]):
                    continue
                # Test if any pair of existing rows work
                for row,_ in possible_rows:
                    M = Matrix(B,2,2,[row,[α,β]])
                    M.set_immutable()
                    if (rn(M) == target_norm if target_norm else rn(M)>0):
                        return M
                possible_rows.append(([α,β], coeffs))
            possible_rows_dict[H] = possible_rows
        else:
            for U,V in itertools.combinations(possible_rows, r=int(2)):
                M = Matrix(B,2,2,[U[0],V[0]])
                if (rn(M) == target_norm if target_norm else rn(M)>0):
                    return M
        print(f"find_kernel_matrices could not find any suitable matrices from {len(possible_rows)} possible rows with coefficients in {coefficients_space}.")
        print(f"Access the possible rows from possible_rows_dict[{H}].")
        return None

def is_polarisation_matrix(M):
    return M[0][0] in ZZ and M[1][1] in ZZ and M[0][0]>0 and M[1][1]>0 and M[0][1] in O and M[0][1].conjugate() == M[1][0] and M[0][0]*M[1][1]-M[0][1]*M[1][0]==1

# From the equation γ*g₂γ = Ng₁ in the paper, we see that γ maps g ↦ sqrt(𝒩(γ)) (γ*)⁻¹ g γ⁻¹.
def apply_polarisation_matrix(γ, g):
    assert pm(g)
    if type(γ) in [int, Integer]: γ = ExE_22_matrices[γ]
    output = hn(γ) * inv(ct(γ)) * g * inv(γ)
    assert rn(output) == 1
    output.set_immutable()
    return output

def matrix_inverse(u):
    a = u[0][0]
    b = u[0][1]
    c = u[1][0]
    d = u[1][1]

    unorm = a.reduced_norm() * d.reduced_norm() + b.reduced_norm() * c.reduced_norm() - (a.conjugate()*b*d.conjugate()*c).reduced_trace()

    M = u * ct(u)
    x = M[0][0]
    y = M[0][1]
    z = M[1][1]
    
    uinv = ct(u) * Matrix(2,2,[z, -y, -(ct(y)), x]) / unorm
    uinv.set_immutable()
    return uinv

def conjugate_transpose(u):
    output = Matrix(B,2,2,[B(β).conjugate() for α in u for β in α]).transpose()
    output.set_immutable()
    return output

def reduced_norm(u):
    if u in B: return u.reduced_norm()
    u = Matrix(B,u)
    rn = (u*ct(u)).determinant()
    return ZZ(rn) if rn in ZZ else QQ(rn)

def hauptnorm(u): return sqrt(Integer(rn(u)))

def ct(u): return u.conjugate() if u in B else conjugate_transpose(u)

def rn(u): return reduced_norm(u)

def hn(u): return hauptnorm(u)

def tr(u): return u.reduced_trace()

def inv(u): return matrix_inverse(u)

def pm(u,g=None): return is_polarisation_matrix(u) if g==None else apply_polarisation_matrix(u,g)

def num_iso_classes(p):
    if not is_prime(p):
        raise ValueError("p must be a prime number")

    leg1 = kronecker(-1, p)
    leg3 = kronecker(-3, p)

    # First part of the expression
    H = (p - 1)*(p^2 + 1)/(2^6 * 3^2 * 5)
    H += 7*(p - 1)^2 / (2^6 * 3^2)
    H += (p - 1)*(1 - leg1)/(2^4 * 3)
    H += (p - 1)*(1 - leg3)/(2^2 * 3^2)
    H += 5*(p - 1)/(2^5 * 3)
    H += (1 - leg1)/(2^5)
    H += (1 - leg3)^2 / 3^2
    H += (1 - leg3)/(2^2 * 3^2)
    H += (p - 1)/(2 * 3^2)
    H += ((1 - leg1)*(1 - leg3))/(2^2 * 3)

    # Additional modular terms
    # Mod 5
    if p == 5:
        H += 1/5
    elif p % 5 == 4:
        H += 4/5
    else:
        H += 0

    # Mod 8
    if p % 8 == 1:
        H += 0
    elif p % 8 == 7:
        H += 1/2
    else:
        H += 1/4

    # Mod 6
    if p % 6 == 1:
        H += 0
    else:
        H += 1/6

    assert H in ZZ
    return ZZ(H)

def random_GL2O_element(n = None):
    if n == None: n = randint(1,3)
    matrices = []
    for i in range(n):
        b = O.random_element()
        c = O.random_element()
        r = randint(0,3)
        if r==0:
            d = O(1)
            a = b*c + 1
        elif r==1:
            a = O(1)
            d = c*b + 1
        elif r==2:
            d = O(-1)
            a = -b*c - 1
        elif r==3:
            a = O(-1)
            d = -c*b - 1
        M = Matrix(B,2,2,[a,b,c,d])
        assert rn(M)==1
        matrices.append(M)
    output = product(matrices)
    output.set_immutable()
    return output

def random_polarisation_matrix():
    r = O.random_element()
    r̄ = ct(r)
    x = divisors(rn(r)+1)
    s = ZZ(choices(x)[0])
    t = ZZ((rn(r)+1)/s)
    M = Matrix(B,2,2,[s,r,r̄,t])
    assert pm(M)
    return M

def random_conjugation(M, must_be_polarisation=True):
    u = random_GL2O_element()
    g = ct(u)*M*u
    count, threshold = 0, 1000
    while must_be_polarisation and not pm(g) and count < threshold:
        count += 1
        u = random_GL2O_element()
        g = conjugate_transpose(u)*M*u
    if count == threshold: raise Exception("Unable to find a conjugation that corresponds to a polarisation.")
    g.set_immutable()
    return g

def matrix_complexity(u):
    return sum(abs(x) for v in u for w in v for x in B(w).coefficient_tuple())

def create_polarisation_22_isogeny_tree():
    graph = DiGraph(loops=True, multiedges=True)
    I = identity_matrix(B,2)
    I.set_immutable()
    graph.vertex_dict = { (): (I, ()) } # Directions: PM, Kernels
    graph.add_vertex(I)
    graph.set_vertex(I, [(), ()]) # PM: Directions, Kernels
    graph.iso_dict = {I: abs_flatten(I)}
    queue1 = [(i,) for i in range(15)]
    queue2 = [() for i in range(15)]
    
    def abs_flatten(M):
        return [abs(ZZ(q)) for elt in change_basis(M) for q in elt]

    def create_graph_(directions : tuple, kernels : tuple):
        print(f"Vertex {directions} | Kernel Index {kernels} | {len(graph)} classes")
        δ = I2 if len(kernels) == 0 else prod([ExE_matrices[k] for k in kernels][::-1])
        g0 = graph.vertex_dict[directions[:-1]][0]
        mats = [(i, pm(ExE_matrices[i], g0)) for i in range(35)]
        inds = [(i,M) for (i,M) in mats if pm(M)]
        assert len(inds) == 15
        ind, g1 = inds[directions[-1]]
        kernels += (ind,)
        # collision = None
        # abs_flatten_g1 = abs_flatten(g1)
        # congruent_g1 = [g1, inv(g1), ct(g1), inv(ct(g1))]
        # for g in graph:
        #     if g in congruent_g1 or abs_flatten_g1 == abs_flatten(g):
        #         print("Collision found!")
        #         collision = g
        #         break
        # if collision != None:
        #     graph.add_edge(g0,collision)
        #     graph.vertex_dict[directions] = (collision, kernels)
        # else:
        #     graph.add_edge(g0,g1)
        #     graph.set_vertex(g1, [directions, kernels])
        #     graph.vertex_dict[directions] = (g1, kernels)

        collision = False
        for g2 in [g1, inv(g1), ct(g1), inv(ct(g1))]:
            if g2 in graph:
                collision = True
                break
        if not collision:
            s = sum(abs_flatten(g1))
            for g2, t in graph.iso_dict:
                if s == t:
                    collision = True
                    break
        if not collision:
            g2 = g1
        graph.add_edge(g0,g2)
        if not collision:
            graph.set_vertex(g1, [directions, kernels])
            graph.iso_dict(g1, sum(abs_flatten(g1)))
        graph.vertex_dict[directions] = (g1, kernels)
        
        if not collision and len(directions) < len(ExE_torsion_basis)-1:
            for i in range(15):
                queue1.append(directions+(i,))
                queue2.append(kernels)
    while queue1:
        create_graph_(queue1.pop(0), queue2.pop(0))

    height = graph.diameter() + 1
    colour_map = plt.get_cmap('Spectral', height)
    colours = [colour_map(c) for c in range(height)]
    colour_dict = dict(zip(colours, [[] for c in range(height)]))
    graph.heights_dict = dict(zip(list(range(-graph.diameter(),1)), [[] for i in range(height)]))
    for matrix,vertex in graph.get_vertices():
        graph.heights_dict[-len(vertex)].append(matrix)
        graph.colour_dict[colour_map(len(vertex))].append(matrix)
    return graph

def load_matrices(single=True):
    matrices = []
    if not single: all_matrices = []
    for i in range(15):
        matrices.append(find_kernel_matrices(i, single=True))
        if not single: all_matrices.append(find_kernel_matrices(i, single=False))
    return matrices if single else (matrices, all_matrices)

def ExE_torsion(n,full=False):
    X,Y = E.torsion_basis(n)
    X1 = EE_Point(X,E(0))
    X2 = EE_Point(E(0),X)
    X3 = EE_Point(Y,E(0))
    X4 = EE_Point(E(0),Y)
    basis = [X1,X2,X3,X4]
    if not full: return basis
    else: return basis, [α1*X1+α2*X2+α3*X3+α4*X4 for α1,α2,α3,α4 in itertools.product(range(n),repeat=4)]

def get_all_ExE_kernels(l=2): # precomputed data, includes non-isotropic kernels
    kernels = None
    matrices = None
    if l==2:
        P = E(0,0)
        Q = E(ω,0)
        R = E(-ω,0)
        Ø = E(0)
        kernels = [
            KernelData(gens=[EE_Point(Q,Ø), EE_Point(Ø,Q)]),
            KernelData(gens=[EE_Point(Q,Ø), EE_Point(Ø,R)]),
            KernelData(gens=[EE_Point(Q,Ø), EE_Point(Ø,P)]),
            KernelData(gens=[EE_Point(R,Ø), EE_Point(Ø,Q)]),
            KernelData(gens=[EE_Point(R,Ø), EE_Point(Ø,R)]),
            KernelData(gens=[EE_Point(R,Ø), EE_Point(Ø,P)]),
            KernelData(gens=[EE_Point(P,Ø), EE_Point(Ø,Q)]),
            KernelData(gens=[EE_Point(P,Ø), EE_Point(Ø,R)]),
            KernelData(gens=[EE_Point(P,Ø), EE_Point(Ø,P)]),
            KernelData(gens=[EE_Point(Q,Q), EE_Point(R,R)]),
            KernelData(gens=[EE_Point(Q,Q), EE_Point(R,P)]),
            KernelData(gens=[EE_Point(Q,R), EE_Point(R,Q)]),
            KernelData(gens=[EE_Point(Q,R), EE_Point(R,P)]),
            KernelData(gens=[EE_Point(Q,P), EE_Point(R,Q)]),
            KernelData(gens=[EE_Point(Q,P), EE_Point(R,R)]),
            # Isotropic vs Non-isotropic separation
            KernelData(gens=[EE_Point(P,Ø), EE_Point(Q,Ø)]),
            KernelData(gens=[EE_Point(Ø,P), EE_Point(Ø,Q)]),
            KernelData(gens=[EE_Point(Q,P), EE_Point(R,P)]),
            KernelData(gens=[EE_Point(P,Q), EE_Point(P,R)]),
            KernelData(gens=[EE_Point(R,P), EE_Point(R,R)]),
            KernelData(gens=[EE_Point(Q,P), EE_Point(Q,R)]),
            KernelData(gens=[EE_Point(Q,P), EE_Point(Q,Q)]),
            KernelData(gens=[EE_Point(R,P), EE_Point(R,Q)]),
            KernelData(gens=[EE_Point(Q,Q), EE_Point(P,Q)]),
            KernelData(gens=[EE_Point(P,Q), EE_Point(R,Q)]),
            KernelData(gens=[EE_Point(P,R), EE_Point(R,R)]),
            KernelData(gens=[EE_Point(P,R), EE_Point(Q,R)]),
            KernelData(gens=[EE_Point(Q,Q), EE_Point(Q,R)]),
            KernelData(gens=[EE_Point(R,R), EE_Point(R,Q)]),
            KernelData(gens=[EE_Point(P,P), EE_Point(P,Q)]),
            KernelData(gens=[EE_Point(P,P), EE_Point(P,R)]),
            KernelData(gens=[EE_Point(R,R), EE_Point(Q,R)]),
            KernelData(gens=[EE_Point(Q,Q), EE_Point(R,Q)]),
            KernelData(gens=[EE_Point(P,P), EE_Point(R,P)]),
            KernelData(gens=[EE_Point(P,P), EE_Point(Q,P)])
        ]
        matrices = [
            matrix(B,[[ii+ω3,-ω4],[ω4,ii+ω3]]),
            matrix(B,[[ii+ω3,ω3],[ω4,1+ω4]]),
            matrix(B,[[ii+ω3+ω4,ω3+ω4],[ii-ω3+ω4,1+ii-ω3+ω4]]),
            matrix(B,[[1+ω4,ω4],[ω3,ii+ω3]]),
            matrix(B,[[ω3,-1-ω4],[1+ω4,ω3]]),
            matrix(B,[[1+ω3+ω4,1+ii+ω3-ω4],[1+ω3-ω4,-ω3-ω4]]),
            matrix(B,[[1+ii+ω3-ω4,ii+ω3-ω4],[ω3+ω4,-ii+ω3+ω4]]),
            matrix(B,[[ω3+ω4,1+ω3+ω4],[1+ii+ω3-ω4,1+ω3-ω4]]),
            matrix(B,[[1+ii,0],[0,1+ii]]),
            matrix(B,[[1,1],[-1,1]]),
            matrix(B,[[ii,ii-ω4],[-ii,ii+ω4]]),
            matrix(B,[[1,ii],[-1,ii]]),
            matrix(B,[[ii,1-ω3],[-ii,1+ω3]]),
            matrix(B,[[1,ii-ω4],[-1,ii+ω4]]),
            matrix(B,[[1,1-ω3],[-1,1+ω3]]),
            # Isotropic vs Non-isotropic separation
            matrix(B,[[2,0],[0,1]]),
            matrix(B,[[1,0],[0,2]]),
            matrix(B,[[0,1+ii],[1+ii,ii]]),
            matrix(B,[[ii,1+ii],[ii+1,0]]),
            matrix(B,[[1,ω4],[-ii,ii+ω3]]),
            matrix(B,[[ii,ω4],[1,ii+ω3]]),
            matrix(B,[[1,1+ω4],[-ii,ω3]]),
            matrix(B,[[1,ω3],[ii,1+ω4]]),
            matrix(B,[[1+ω4,-1],[ω3,ii]]),
            matrix(B,[[ω4,ii],[ii+ω3,1]]),
            matrix(B,[[ω4,-1],[ii+ω3,ii]]),
            matrix(B,[[ω3,1],[1+ω4,ii]]),
            matrix(B,[[1,1+ii+ω3-ω4],[ii,ω3+ω4]]),
            matrix(B,[[1,ω3+ω4],[-ii,1+ii+ω3-ω4]]),
            matrix(B,[[ii,1+ω3-ω4],[-1,1+ω3+ω4]]),
            matrix(B,[[1,ii-ω3+ω4],[-ii,ii+ω3+ω4]]),
            matrix(B,[[1+ii+ω3-ω4,-ii],[ω3+ω4,1]]),
            matrix(B,[[1+ii+ω3-ω4,1],[ω3+ω4,ii]]),
            matrix(B,[[ii+ω3-ω4,-ii],[-ii+ω3+ω4,1]]),
            matrix(B,[[1+ω3-ω4,1],[1+ω3+ω4,ii]])
        ]
    elif l==3:
        ExE_3_torsion_basis = ExE_torsion(3)
        V = VectorSpace(GF(3), 4)
        kernels = []
        for S in V.subspaces(2):
            coeffs = S.basis()
            basis = [EE_Point.sum(ExE_3_torsion_basis[i] * coeffs[j][i] for i in range(4)) for j in range(2)]
            kernels.append(KernelData(coeffs, basis))
        kernels.sort(key = lambda K : not K.is_isotropic)
        matrices = [
            matrix(B,[(1 + kk, -2*ii - jj), (2*ii + jj, 1 + kk)]),
            matrix(B,[(1 + kk, 2 + kk), (2*ii + jj, ii + jj)]),
            matrix(B,[(1/2 + 1/2*ii - 1/2*jj + 1/2*kk, 2*ii + kk), (2*ii + jj, -1 + ii + jj - kk)]),
            matrix(B,[(ii, 1/2 - 3/2*ii - 1/2*jj - 1/2*kk), (ii, 1/2 + 3/2*ii - 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, 1 - ii), (ii, 1 + 2*ii)]),
            matrix(B,[(ii, 3/2 - 1/2*ii + 1/2*jj + 1/2*kk), (ii, 3/2 + 5/2*ii + 1/2*jj + 1/2*kk)]),
            matrix(B,[(ii, -1/2 + 3/2*ii + 1/2*jj + 1/2*kk), (ii, -1/2 - 3/2*ii + 1/2*jj + 1/2*kk)]),
            matrix(B,[(ii, -1 + ii), (ii, -1 - 2*ii)]),
            matrix(B,[(ii, -3/2 + 1/2*ii - 1/2*jj - 1/2*kk), (ii, -3/2 - 5/2*ii - 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii + jj, 2*ii + jj), (2 + kk, 1 + kk)]),
            
            matrix(B,[(ii + jj, -2 - kk), (2 + kk, ii + jj)]),
            matrix(B,[(2 + kk, 3 - ii + kk), (1/2 + 1/2*ii + 1/2*jj - 1/2*kk, -1/2 + 1/2*ii + 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, 1 + ii), (ii, 1 - 2*ii)]),
            matrix(B,[(ii, 1/2 - 3/2*ii - 1/2*jj + 1/2*kk), (ii, 1/2 + 3/2*ii - 1/2*jj + 1/2*kk)]),
            matrix(B,[(ii, -3/2 + 1/2*ii + 1/2*jj - 1/2*kk), (ii, 3/2 + 1/2*ii + 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, -1 - ii), (ii, -1 + 2*ii)]),
            matrix(B,[(ii, -1/2 + 3/2*ii + 1/2*jj - 1/2*kk), (ii, -1/2 - 3/2*ii + 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, 3/2 - 1/2*ii - 1/2*jj + 1/2*kk), (ii, -3/2 - 1/2*ii - 1/2*jj + 1/2*kk)]),
            matrix(B,[(1/2 + ii + jj + 1/2*kk, 1/2 + 2*ii + jj + 1/2*kk), (2 + 1/2*ii - 1/2*jj + kk, 1 + 1/2*ii - 1/2*jj + kk)]),
            matrix(B,[(1/2 + ii + jj + 1/2*kk, -1/2 + ii + jj + 1/2*kk), (2 + 1/2*ii - 1/2*jj + kk, 2 - 1/2*ii - 1/2*jj + kk)]),

            matrix(B,[(-1/2 + 1/2*ii + 1/2*jj - 1/2*kk, -1/2 - 1/2*ii + 1/2*jj + 1/2*kk), (1 + 1/2*ii + 1/2*jj + kk, 5/2 - 2*ii - jj + 1/2*kk)]),
            matrix(B,[(ii, 3/2 + 1/2*ii + 1/2*jj + 1/2*kk), (ii, -3/2 + 1/2*ii + 1/2*jj + 1/2*kk)]),
            matrix(B,[(ii, -3/2 - 1/2*ii + 1/2*jj - 1/2*kk), (ii, -3/2 + 5/2*ii + 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, 3/2*ii + 1/2*jj), (ii, -3/2*ii + 1/2*jj)]),
            matrix(B,[(ii, -3/2 - 1/2*ii - 1/2*jj - 1/2*kk), (ii, 3/2 - 1/2*ii - 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, 3/2 + 1/2*ii - 1/2*jj + 1/2*kk), (ii, 3/2 - 5/2*ii - 1/2*jj + 1/2*kk)]),
            matrix(B,[(ii, -3/2*ii - 1/2*jj), (ii, 3/2*ii - 1/2*jj)]),
            matrix(B,[(ii, 1/2 + 3/2*ii + 1/2*jj + 1/2*kk), (ii, 1/2 - 3/2*ii + 1/2*jj + 1/2*kk)]),
            matrix(B,[(ii, 3/2 + 1/2*kk), (ii, -3/2 + 1/2*kk)]),
            matrix(B,[(ii, -1/2 - 3/2*ii - 1/2*jj + 1/2*kk), (ii, -1/2 + 3/2*ii - 1/2*jj + 1/2*kk)]),
            
            matrix(B,[(ii, -1/2 - 3/2*ii - 1/2*jj - 1/2*kk), (ii, -1/2 + 3/2*ii - 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, 1/2 + 3/2*ii + 1/2*jj - 1/2*kk), (ii, 1/2 - 3/2*ii + 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, -3/2 - 1/2*kk), (ii, 3/2 - 1/2*kk)]),
            matrix(B,[(1/2 + 1/2*ii - 1/2*jj + 1/2*kk, 2 - jj), (2*ii + jj, 1 + ii + jj + kk)]),
            matrix(B,[(2 + kk, -1 - 3*ii - jj), (1/2 + 1/2*ii + 1/2*jj - 1/2*kk, 1/2 + 1/2*ii + 1/2*jj + 1/2*kk)]),
            matrix(B,[(-1/2 + 1/2*ii + 1/2*jj - 1/2*kk, 1/2 - 1/2*ii + 1/2*jj - 1/2*kk), (1 + 1/2*ii + 1/2*jj + kk, 2 + 5/2*ii + 1/2*jj + kk)]),
            matrix(B,[(-1/2 + ii + jj - 1/2*kk, 1/2 - 2*ii - jj + 1/2*kk), (2 - 1/2*ii + 1/2*jj + kk, -1 + 1/2*ii - 1/2*jj - kk)]),
            matrix(B,[(-1/2 + ii + jj - 1/2*kk, 1/2 + ii + jj - 1/2*kk), (2 - 1/2*ii + 1/2*jj + kk, 2 + 1/2*ii + 1/2*jj + kk)]),
            matrix(B,[(1/2 + 1/2*ii + 1/2*jj + 1/2*kk, 1/2 + 1/2*ii - 1/2*jj - 1/2*kk), (-1 + 1/2*ii + 1/2*jj - kk, 2 - 5/2*ii - 1/2*jj + kk)]),
            matrix(B,[(1/2 + 1/2*ii + 1/2*jj + 1/2*kk, -1/2 + 1/2*ii - 1/2*jj + 1/2*kk), (-1 + 1/2*ii + 1/2*jj - kk, 5/2 + 2*ii + jj + 1/2*kk)]),
            
            # Isotropic vs Non-isotropic separation

            matrix(B,[(1 + kk, ii), (2*ii + jj, 1)]),
            matrix(B,[(1 + kk, 1), (2*ii + jj, -ii)]),
            matrix(B,[(1/2 + 1/2*ii - 1/2*jj + 1/2*kk, 1/2 - 3/2*ii - 1/2*jj - 1/2*kk), (2*ii + jj, 1 + ii + kk)]),
            matrix(B,[(1 + kk, -ii), (2*ii + jj, -1)]),
            matrix(B,[(1 + kk, -1), (2*ii + jj, ii)]),
            matrix(B,[(1/2 + 1/2*ii - 1/2*jj + 1/2*kk, -1/2 + 3/2*ii + 1/2*jj + 1/2*kk), (2*ii + jj, -1 - ii - kk)]),
            matrix(B,[(ii, 1 + kk), (1, 2*ii + jj)]),
            matrix(B,[(ii, -ii - jj), (1, 2 + kk)]),
            matrix(B,[(ii, 1/2 + ii + jj + 1/2*kk), (1, -2 - 1/2*ii + 1/2*jj - kk)]),
            matrix(B,[(ii, -3/2 + 3/2*ii + 1/2*jj - 1/2*kk), (ii, -3/2 - 3/2*ii + 1/2*jj - 1/2*kk)]),

            matrix(B,[(ii, -1 + 1/2*ii - 1/2*jj), (ii, -1 - 5/2*ii - 1/2*jj)]),
            matrix(B,[(ii, -1/2 + ii + 1/2*kk), (ii, -1/2 - 2*ii + 1/2*kk)]),
            matrix(B,[(ii, -1 - kk), (1, -2*ii - jj)]),
            matrix(B,[(ii, ii + jj), (1, -2 - kk)]),
            matrix(B,[(ii, -1/2 - ii - jj - 1/2*kk), (1, 2 + 1/2*ii - 1/2*jj + kk)]),
            matrix(B,[(ii, 3/2 - 3/2*ii - 1/2*jj + 1/2*kk), (ii, 3/2 + 3/2*ii - 1/2*jj + 1/2*kk)]),
            matrix(B,[(ii, 1 - 1/2*ii + 1/2*jj), (ii, 1 + 5/2*ii + 1/2*jj)]),
            matrix(B,[(ii, 1/2 - ii - 1/2*kk), (ii, 1/2 + 2*ii - 1/2*kk)]),
            matrix(B,[(-ii - jj, ii), (2 + kk, 1)]),
            matrix(B,[(-ii - jj, 1), (2 + kk, -ii)]),
            
            matrix(B,[(2 + kk, 3 + ii + jj + kk), (1/2 + 1/2*ii + 1/2*jj - 1/2*kk, -1 + ii - kk)]),
            matrix(B,[(-ii - jj, -ii), (2 + kk, -1)]),
            matrix(B,[(-ii - jj, -1), (2 + kk, ii)]),
            matrix(B,[(2 + kk, -3 - ii - jj - kk), (1/2 + 1/2*ii + 1/2*jj - 1/2*kk, 1 - ii + kk)]),
            matrix(B,[(ii, -1/2*ii + 1/2*jj), (ii, 5/2*ii + 1/2*jj)]),
            matrix(B,[(ii, -1/2 + 1/2*kk), (ii, 5/2 + 1/2*kk)]),
            matrix(B,[(ii, 1/2 + 1/2*ii - 1/2*jj - 1/2*kk), (ii, 1/2 - 5/2*ii - 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, -1 - 1/2*ii - 1/2*jj), (ii, 2 - 1/2*ii - 1/2*jj)]),
            matrix(B,[(ii, 3/2 + 3/2*ii + 1/2*jj + 1/2*kk), (ii, 3/2 - 3/2*ii + 1/2*jj + 1/2*kk)]),
            matrix(B,[(ii, -1/2 - ii - 1/2*kk), (ii, -1/2 + 2*ii - 1/2*kk)]),
            
            matrix(B,[(ii, 1/2*ii - 1/2*jj), (ii, -5/2*ii - 1/2*jj)]),
            matrix(B,[(ii, 1/2 - 1/2*kk), (ii, -5/2 - 1/2*kk)]),
            matrix(B,[(ii, -1/2 - 1/2*ii + 1/2*jj + 1/2*kk), (ii, -1/2 + 5/2*ii + 1/2*jj + 1/2*kk)]),
            matrix(B,[(ii, 1 + 1/2*ii + 1/2*jj), (ii, -2 + 1/2*ii + 1/2*jj)]),
            matrix(B,[(ii, -3/2 - 3/2*ii - 1/2*jj - 1/2*kk), (ii, -3/2 + 3/2*ii - 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, 1/2 + ii + 1/2*kk), (ii, 1/2 - 2*ii + 1/2*kk)]),
            matrix(B,[(-1/2 - ii - jj - 1/2*kk, -ii), (2 + 1/2*ii - 1/2*jj + kk, -1)]),
            matrix(B,[(-1/2 - ii - jj - 1/2*kk, -1), (2 + 1/2*ii - 1/2*jj + kk, ii)]),
            matrix(B,[(-1/2 + 1/2*ii + 1/2*jj - 1/2*kk, 3/2 + 3/2*ii + 1/2*jj + 1/2*kk), (1 + 1/2*ii + 1/2*jj + kk, -3/2 - jj + 1/2*kk)]),
            matrix(B,[(-1/2 - ii - jj - 1/2*kk, ii), (2 + 1/2*ii - 1/2*jj + kk, 1)]),
            
            matrix(B,[(-1/2 - ii - jj - 1/2*kk, 1), (2 + 1/2*ii - 1/2*jj + kk, -ii)]),
            matrix(B,[(-1/2 + 1/2*ii + 1/2*jj - 1/2*kk, 1 + ii), (1 + 1/2*ii + 1/2*jj + kk, -2 + ii)]),
            matrix(B,[(ii, 1/2 + 1/2*ii - 1/2*jj + 1/2*kk), (ii, 1/2 - 5/2*ii - 1/2*jj + 1/2*kk)]),
            matrix(B,[(ii, 1/2 - 1/2*ii - 1/2*jj - 1/2*kk), (ii, -5/2 - 1/2*ii - 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, -1 - 3/2*ii - 1/2*jj), (ii, -1 + 3/2*ii - 1/2*jj)]),
            matrix(B,[(ii, -1/2 - ii + 1/2*kk), (ii, -1/2 + 2*ii + 1/2*kk)]),
            matrix(B,[(ii, -1/2 + ii - 1/2*kk), (ii, -1/2 - 2*ii - 1/2*kk)]),
            matrix(B,[(ii, 1), (ii, -2)]),
            matrix(B,[(ii, -1/2 - 1/2*ii + 1/2*jj - 1/2*kk), (ii, -1/2 + 5/2*ii + 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, -1/2 + 1/2*ii + 1/2*jj + 1/2*kk), (ii, 5/2 + 1/2*ii + 1/2*jj + 1/2*kk)]),
            
            matrix(B,[(ii, 1 + 3/2*ii + 1/2*jj), (ii, 1 - 3/2*ii + 1/2*jj)]),
            matrix(B,[(ii, 1/2 + ii - 1/2*kk), (ii, 1/2 - 2*ii - 1/2*kk)]),
            matrix(B,[(ii, 1/2 - ii + 1/2*kk), (ii, 1/2 + 2*ii + 1/2*kk)]),
            matrix(B,[(ii, -1), (ii, 2)]),
            matrix(B,[(-3/2 - 3/2*kk, -1), (-3/2*ii - 3/2*jj, ii)]),
            matrix(B,[(1/2 + 1/2*ii - 1/2*jj + 1/2*kk, 3/2 - 1/2*ii - 1/2*jj - 1/2*kk), (2*ii + jj, 1 - ii + kk)]),
            matrix(B,[(1/2 + 1/2*ii - 1/2*jj + 1/2*kk, -3/2 + 1/2*ii + 1/2*jj + 1/2*kk), (2*ii + jj, -1 + ii - kk)]),
            matrix(B,[(1/2 + 1/2*ii + 1/2*jj + 1/2*kk, 1 - ii), (-1 + 1/2*ii + 1/2*jj - kk, -2 - ii)]),
            matrix(B,[(-1/2 + 1/2*ii + 1/2*jj - 1/2*kk, 1 - ii), (1 + 1/2*ii + 1/2*jj + kk, 1 + 2*ii)]),
            matrix(B,[(2 + kk, -1 - ii), (1/2 + 1/2*ii + 1/2*jj - 1/2*kk, ii)]),
            
            matrix(B,[(1/2 + 1/2*ii + 1/2*jj + 1/2*kk, 3/2 - 3/2*ii - 1/2*jj + 1/2*kk), (-1 + 1/2*ii + 1/2*jj - kk, -3/2 + jj + 1/2*kk)]),
            matrix(B,[(2 + kk, 1 + ii), (1/2 + 1/2*ii + 1/2*jj - 1/2*kk, -ii)]),
            matrix(B,[(-1/2 + 1/2*ii + 1/2*jj - 1/2*kk, 3/2 - 3/2*ii - 1/2*jj + 1/2*kk), (1 + 1/2*ii + 1/2*jj + kk, 3/2*ii - 1/2*jj - kk)]),
            matrix(B,[(1/2 - ii - jj + 1/2*kk, -ii), (2 - 1/2*ii + 1/2*jj + kk, -1)]),
            matrix(B,[(ii, -ii), (ii, 2*ii)]),
            matrix(B,[(1/2 - ii - jj + 1/2*kk, -1), (2 - 1/2*ii + 1/2*jj + kk, ii)]),
            matrix(B,[(ii, -1 + 1/2*ii + 1/2*jj), (ii, 2 + 1/2*ii + 1/2*jj)]),
            matrix(B,[(1/2 + 1/2*ii + 1/2*jj + 1/2*kk, 3/2 + 3/2*ii + 1/2*jj + 1/2*kk), (-1 + 1/2*ii + 1/2*jj - kk, -3/2*ii + 1/2*jj - kk)]),
            matrix(B,[(ii, 1 + 1/2*ii - 1/2*jj), (ii, 1 - 5/2*ii - 1/2*jj)]),
            matrix(B,[(1/2 - ii - jj + 1/2*kk, ii), (2 - 1/2*ii + 1/2*jj + kk, 1)]),
            
            matrix(B,[(ii, ii), (ii, -2*ii)]),
            matrix(B,[(1/2 + 1/2*ii + 1/2*jj + 1/2*kk, 1 + ii), (-1 + 1/2*ii + 1/2*jj - kk, 1 - 2*ii)]),
            matrix(B,[(ii, -1 - 1/2*ii + 1/2*jj), (ii, -1 + 5/2*ii + 1/2*jj)]),
            matrix(B,[(1/2 - ii - jj + 1/2*kk, 1), (2 - 1/2*ii + 1/2*jj + kk, -ii)]),
            matrix(B,[(ii, 1 - 1/2*ii - 1/2*jj), (ii, -2 - 1/2*ii - 1/2*jj)]),
            matrix(B,[(ii, -1/2 + ii + jj - 1/2*kk), (1, -2 + 1/2*ii - 1/2*jj - kk)]),
            matrix(B,[(ii, 1/2 - 1/2*ii + 1/2*jj - 1/2*kk), (ii, 1/2 + 5/2*ii + 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, -3/2 + ii - 1/2*kk), (ii, -3/2 - 2*ii - 1/2*kk)]),
            matrix(B,[(ii, 1/2 - ii - jj + 1/2*kk), (1, 2 - 1/2*ii + 1/2*jj + kk)]),
            matrix(B,[(ii, -1/2 + 1/2*ii - 1/2*jj + 1/2*kk), (ii, -1/2 - 5/2*ii - 1/2*jj + 1/2*kk)]),
            
            matrix(B,[(ii, 3/2 - ii + 1/2*kk), (ii, 3/2 + 2*ii + 1/2*kk)]),
            matrix(B,[(ii, 1/2 - 1/2*ii + 1/2*jj + 1/2*kk), (ii, 1/2 + 5/2*ii + 1/2*jj + 1/2*kk)]),
            matrix(B,[(ii, -1/2 + 1/2*ii - 1/2*jj - 1/2*kk), (ii, -1/2 - 5/2*ii - 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, -1/2 - 1/2*ii - 1/2*jj + 1/2*kk), (ii, 5/2 - 1/2*ii - 1/2*jj + 1/2*kk)]),
            matrix(B,[(ii, 1/2 + 1/2*ii + 1/2*jj - 1/2*kk), (ii, -5/2 + 1/2*ii + 1/2*jj - 1/2*kk)]),
            matrix(B,[(ii, 3/2 + ii + 1/2*kk), (ii, 3/2 - 2*ii + 1/2*kk)]),
            matrix(B,[(ii, -3/2 - ii - 1/2*kk), (ii, -3/2 + 2*ii - 1/2*kk)]),
            matrix(B,[(-1/2 - 1/2*kk, -3), (1/2*ii + 1/2*jj, -3*ii)]),
            matrix(B,[(ii, 1 - 3/2*ii - 1/2*jj), (ii, 1 + 3/2*ii - 1/2*jj)]),
            matrix(B,[(ii, -1 + 3/2*ii + 1/2*jj), (ii, -1 - 3/2*ii + 1/2*jj)]),
        ]
    return kernels, matrices

def ExE_automorphisms():
    AutE = []
    α = E.automorphisms()[2]
    a=SSpecPPAS_Isogeny([ExE.infinity], ExE, ExE, lambda R : EE_Point(α(R.P), R.Q))
    b=SSpecPPAS_Isogeny([ExE.infinity], ExE, ExE, lambda R : EE_Point(R.P, α(R.Q)))
    τ=SSpecPPAS_Isogeny([ExE.infinity], ExE, ExE, lambda R : EE_Point(R.Q, R.P))
    for i,j,k in itertools.product(range(4),range(4),range(2)):
        AutE.append(τ.power(k).compose(b.power(j)).compose(a.power(i)))
    return AutE

def flatten(M):
    return [q for elt in change_basis(M) for q in elt]

def ideal_to_kernel(I, linearly_independent=False):
    α,DI = I.gens() # DI is D * I2
    α = Matrix(B,α)
    D = sqrt(hn(Matrix(B,DI)))
    assert rn(α) % D^2 == 0
    
    β = [] # basis for M2O
    β.extend([Matrix(B,2,2,[q,0,0,0]) for q in O.basis()])
    β.extend([Matrix(B,2,2,[0,q,0,0]) for q in O.basis()])
    β.extend([Matrix(B,2,2,[0,0,q,0]) for q in O.basis()])
    β.extend([Matrix(B,2,2,[0,0,0,q]) for q in O.basis()])
    vα = [mod(q,D) for q in flatten(α)]

    torsion = ExE_torsion(D)
    Ms = []
    for i in range(16):
        images = evaluate_matrix_on_point(β[i], torsion)
        dlog = [[mod(q,D) for q in R.log(torsion)] for R in images]
        Ms.append(Matrix(4,4,dlog))

    Mα = sum(vα[i]*Ms[i] for i in range(16))
    ker_coeffs = Mα.kernel().gens()
    ker_gens = [EE_Point.sum(K[j]*torsion[j] for j in range(4)) for K in ker_coeffs]
    if linearly_independent: ker_gens = make_linearly_independent(ker_gens)
    assert matrix_has_kernel(α,ker_gens), "Kernel calculation failed; check that |ker α| = N(α) = D²"
    return ker_gens
    
def find_kernel(α, n): # α is an isogeny matrix
    return set(R for R in ExE_torsion(n,True)[1] if matrix_has_kernel(α,[R]))

def kernel_gens(α, n): # α is an isogeny matrix
    kernel = find_kernel(α, n)
    ker_size = len(kernel)
    for rank in range(2,4):
        for pts in itertools.combinations(kernel, r=rank):
            if len(EE_Point.span(pts)) == ker_size and prod(R.order() for R in pts) == ker_size:
                return pts

def make_linearly_independent(gens): # gens is a spanning set of an isogeny kernel
    gens.sort(key = lambda R : -R.order())
    output = []
    inf = {ExE.infinity}
    span = {ExE.infinity}
    for R_ in gens:
        for S in list(inf) + list(span):
            R = R_ + S
            spanR = EE_Point.span(R) - inf
            if spanR.isdisjoint(span):
                output.append(R)
                span |= {S+T for S in spanR for T in span}
                break
        else:
            print("An error occured, falling back to naïve method")
            kernel = EE_Point.span(gens)
            ker_size = len(kernel)
            for rank in range(2,5):
                for pts in itertools.combinations(kernel, r=rank):
                    if len(EE_Point.span(pts)) == ker_size and prod(R.order() for R in pts) == ker_size:
                        return pts
    return output

if 'p' not in globals() or p == None: p=2591 # 2⁵×3⁴-1
assert p%4==3 and p%3==2
F.<ω>=GF(p^2, 'ω', modulus=[1,0,1])
_.<x> = F[]
E = EllipticCurve(F, j=1728)
B.<ii,jj,kk> = QuaternionAlgebra(-1,-p) # use ii, jj, kk to avoid clash with i, j, k for indexing
ω3 = (ii+jj)/2
ω4 = (1+kk)/2
O = B.quaternion_order([B(1),ii,(ii+jj)/2,(B(1)+kk)/2])
M2O = MatrixSpace(O,2)
H = num_iso_classes(p)
ExE = SSpecPPAS(E)
I2 = identity_matrix(B,2)
ExE_22_kernels, ExE_22_matrices = get_all_ExE_kernels(2)

possible_rows_dict = dict()