###############################################################################
# This software allows one to compute the degree of certain field extensions  #
# of the rational numbers. In particular, it can compute the degree over Q of #
# extensions of the form Q( sqrt[N](G), \zeta_M ), where:                     #
#  - N and M are integers with N dividing M;                                  #
#  - G is a finitely generated subgroup of the multiplicative group of Q      #
#  - \zeta_M is a primitive M-th root of unity                                #
# The group G does not have to be given in a particular format. A finite set  #
# of generators is sufficient.                                                #
###############################################################################

# Computes the "adelic Kummer failure", i.e. the degrees of the intersection
# of the the Kummer extension Q(\sqrt{2^n}{G}) with the M-th cyclotomic field
# over Q_{2^n}.
#
# Input: a good basis B for the torsion-free group G, organized as a list of
# lists, and a non negative integer d. They have to satisfy the following:
# 1. Each list B[i] contains all basis elements of 2-divisibility i.
# 2. The basis given by B is 2-maximal, that is to say it satisfies Theorem 14
#    of Debry-Perucca; i.e. each element of B[i] is, up to plus or minus 1, the
#    2^i-th power of a strongly 2-indivisible rational.
# 3. For i != d every element of B[i] is positive, and B[d][0] is the only
#    negative element of B[d] (if d=-1, then there is no negative element).
# 3'. Notice that the existence on negative elements in B[0] does not influence
#    the correctness of the algorithm; in fact, the function adjust_sign
#    produces a basis that may have negative elements of divisibility 0, and
#    this basis is given as input for adelic_failure_gb.
#
# Output: a table ad_fail as described below. Call M0 the smallest positive
# integer such that the intersection of Q(\sqrt{2^n}{G}) with Q_\infty is
# contained in Q_M0.
# The table ad_fail has N rows, where N is defined below.
# Each row R=ad_fail[i] contains a variable number of pairs (d,r), where d is a
# divisor of M0 and r is the degree of Q(\sqrt{2^{i+1}}{G}) \cap Q_d over
# Q_{2^n}.
# Each divisor of M appears at most once on each row, and the last element of
# the last row is of the form (M0,r0).
def adelic_failure_gb( B, d ):

    # The table to be returned (or printed at the end), as described above.
    ad_fail = []

    # N is such that for every n > N the adelic failure of Q(\sqrt{2^n}{G}) is
    # the same as that of Q(\sqrt{2^N}{G}).
    # We always have to include n=3, because of problem with sqrt(2) in Q_8 (in
    # theory, this is not necessary in some cases, e.g. if 2 does not divide
    # any element of G).
    # If the negative generator is on the last level, we need to increase N by
    # 1, because it would contribute to the shortlist in the next level (by
    # taking the root of an even power).
    if d == len(B)-1:
        N = max(3,len(B)+1)
    else:
        N = max(3,len(B))

    # The intersection is given by adding the square roots of the elements of
    # this shortlist (and a "special element", not always of the form sqrt(d),
    # coming from taking a suitable root of a negative generator; this special
    # element is dealt with later). The shortlist grows at each step, so we
    # declare it before starting to loop over n and we build it incrementally.
    # The "special element" is of the form \zeta_{2^n}\sqrt{b}, which we encode
    # as (n,b). We use the value (1,1) (special element -1) to say that there
    # isno special element at this level.
    shortlist = []
    special_element = (1,1)

    # The integers M, giving the smallest cyclotomic field in which lies the
    # whole intersection with Q_\infty, also grows with n. As with the
    # shortlist, we declare it here and increase it appropriately at each step.
    M = 1

    for n in range( 1, N+1 ):

        # We add the new elements to the shortlist, modifying M if needed.
        # This is not done in case we are in the extra "fake" level (this case
        # dealt with immediately below).
        if n-1 < len(B):
            for g in B[n-1]:
                # Case of negative g
                if g < 0 and n > 1:
                    # Special element of the form \zeta_{2^{n+1}}\sqrt(b).
                    # It is contained in Q_{lcm(2^{n+1},cyc_emb(b))}, except in 
                    # case n=2 and b=2, in which case it is contained in Q_4.
                    # We store it as as pair ( n+1, b ).
                    special_element = ( n+1, abs(g)^(1/(2^(n-1))) )
                    M = lcm( M, special_embed( special_element ) )
                else:
                    b = g^(1/(2^(n-1))) # b is 2-indivisible
                    shortlist.append( b )
                    M = lcm( M, cyc_embed(b) )

        # We add a root of an even power of the negative generator, as soon as
        # we are beyond its level.
        if d != -1 and n == d+2:        
            b = abs(B[d][0])^(1/2^d)
            shortlist.append( b ) 
            M = lcm( M, cyc_embed(b) )

        M = lcm(M,2^n)
            
        # Here we account for the extra 2^{n+1} root of unity (in case the
        # negative element has enough divisibility).
        if n <= d:
            M = lcm( M, 2^(n+1) )

        # We have to add -1 to the shortlist (see example [12,36]) and
        # remove it later.
        if n == 1 and d >= 1:
            shortlist.append(-1)
        if n > 1 and -1 in shortlist:
            shortlist.remove(-1)

        # For each divisor dM of M, compute the degree of the intersection of
        # Q(\sqrt{2^n}{G}) with Q_dM over Q_{2^n}. We need to compute the
        # number r of elements in the subgroup of G generated by the shortlist
        # that lie in Q_dM. This is going to be a power of 2. The sought degree
        # will be r, up to considering some special cases (described below).
        # 
        # This algorithm could be inefficient for groups of big rank. It can be
        # improved by precomputing subgroups of G/G^2 and the cyclotomic fields
        # containing them.

        aux = [] # Next line of ad_fail table

        for dM in divisors( M ):
            # We only care of the intersection with Q_dM if it contains the 2^n
            # roots of unity.
            if dM % (2^n) != 0:
                continue

            # The following line gives, without repetitions, the list of m's
            # such that that some element in the subgroup of G generated by
            # the shortlist embeds in Q_m.
            S = [ product(s) for s in subsets( shortlist ) ]
            H = [ cyc_embed( s ) for s in S ] 
            r = len( [ b for b in H if dM % b == 0 ] )
            
            # We double n in case a new roots of unity enters the cyclotomic
            # due to the negative negerator. In case n=1, this is accounted
            # by having -1 in the shortlist.
            if n <= d and dM % (2^(n+1)) == 0 and n > 1:
                r *= 2

            # We loose a factor of 2 if we have sqrt(2) in Q_8 or \zeta_8 2 in
            # Q_4.
            if 8 in H and dM % 8 == 0 and (n >= 3 or (n == 2 and n <= d)):
                r = r/2

            # If we have a special element in this level, we consider it.
            # We have to consider all possible special elements arising from
            # multiplying the given element with the other elements of the
            # shortlist.
            # If any of them is of the form \zeta_8 2q for q a square, there is
            # nothing to do: in fact \zeta_8 2 embeds in Q_4, which coincides
            # with Q_{2^n} (n must be 2); so we would double the degree because
            # of the existence of the special element, butthen we would loose
            # another factor of 2 because of this.
            if special_element != (1,1) and special_element[0] == n+1:
                nothing_to_do = False
                intersecting_QdM = False
                for s in S:
                    new_special = ( n+1, special_element[1] * s )
                    m = special_embed( new_special )
                    if n == 2 and m == 4: # \zeta_8 times 2 times square
                        nothing_to_do = True
                    if dM % m == 0:
                        intersecting_QdM = True
                if intersecting_QdM and not nothing_to_do:
                    r *= 2

            aux.append( (dM,r) )
        
        ad_fail.append(aux)

    return ad_fail

# Returns the smallest m such that \sqrt(b) is in the m-th cyclotomic field.
def cyc_embed( b ):
    m = squarefree_part(b)
    if m%4 != 1:
        m *= 4
    return abs(m)

# Computes the minimal cyclotomic field containing \zeta_{2^n}\sqrt(b).
def special_embed( (n,b) ):
    m = squarefree_part(b)
    if n == 3 and m % 2 == 0:
        return 4 * cyc_embed(m/2)
    else:
        return lcm( 2^n, cyc_embed(b) )

# Computes the "l-adic failure", i.e. the ratio between l^{nr} and the degree
# of Q_{l^m}(\sqrt[2^n](G)) over Q_{l^m} for all possible l.
# Input: any basis for G
# Returns a pair (L,T) where:
#   - L is a list of primes l that do not have maximal l-adic part
#   - T is an array of tables, where T[i][m][n] is the l-valuation of the
#     degree of Q_{l^m,l^n} over Q_{l^m}, where l = L[i]
def total_l_adic_failure( B ):

    bp = bad_primes(B)
    ret = ( bp, [] )

    for l in bp:
        ret[1].append( l_adic_failure( B, l ) )

    return ret

# Computes the "bad primes", i.e. the ones for which the l-adic part is not
# maximal. Used by total_l_adic_failure.
def bad_primes( B ):
    M = exponent_matrix( B )
    (a,b) = M.dimensions()

    if a > b or M.rank() < a:
        print "This is not a basis"
        return

    # Compute which primes l divide all minors of the exponent matrix
    bad_primes = list( prime_factors( gcd( M.minors(a) ) ) )
    if 2 not in bad_primes:
        bad_primes += [2] # 2 is always bad

    return sorted(bad_primes) # Ensures 2 is always first
   
# Computes the l-adic failure for a specific l. Returns a "table" as described
# above "total_l_adic_failure".
# B is any basis for G.
def l_adic_failure( B, l ):

    r = len(B)
    GB = make_good_basis( B, l )
    
    # Computes the parameters over Q4. For l odd, they are the same as over Q.
    p = parameters_Q4( GB, l )
    maxM = max( [ sum(x) for x in p ] )
    maxN = max( maxM, len(GB)-1 )

    maxM = max( 1, maxM )
    if l == 2:
        maxM = max( 2, maxM ) # For computing parameters over Q4
    maxN = max( 1, maxN )

    tabel = []
    max_failure = 0
    for m in range( 1, maxM+1 ):
        row = []
        for n in range( 1, max( m+1, maxN ) ):
            vl = -1
            if m >= n:
                if l==2 and n==1 and m==1:
                    vl = compute_vl( p, 1, 2, r )
                    if adjust_sign( GB )[1] >= 1:
                        vl += 1
                else:
                    vl = compute_vl( p, n, m, r )
                failure = r*n - vl
            row.append(vl)
            max_failure = max( max_failure, failure )
        tabel.append((row,max_failure))
    return tabel

# Returns a power of l that is the l-adic failure at M, N.
# tablel must be the output table of l_adic_failure.
def l_adic_failure_from_data( B, l, tablel, M, N ):

    m = valuation( M, l )
    n = valuation( N, l )
    if m < n:
        # inconsistent choice of M and N
        return 0
    if n == 0:
        return 1
    r = len(B)

    if m > len(tablel):
        if n > len(tablel):
            return l^tablel[-1][1]
        else:
            return l^(r*n-tablel[-1][0][n-1])
    
    return l^(r*n-tablel[m-1][0][n-1])

# Returns the l-dvisibility parameters of G over Q, given a good basis gb of G,
# as a list of pairs (di,hi).
def parameters_Q( gb, l ):
    #ret = []
    #for i in range( len( gb ) ):
    #    for j in gb[i]:
    #        ret.append( (i,0) )
    #return ret
    return [x for a in [[(i,0)]*len(gb[i]) for i in range(len(gb))] for x in a]

# Computes the l-divisibility parameters of G over Q4, given a good basis gb
# over Q for G. Returns a list of pairs (di,hi).
# If l is odd it just uses the good basis given to compute the parameters.
# If l=2, it uses the results of PST-2.
def parameters_Q4( gb, l ):
    if l != 2:
        return parameters_Q( gb, l )
    else:
        # Converts from "good basis format" to simple list
        #b = []
        #for x in gb:
        #    b += x
        b = [ x for a in gb for x in a ]
    
        M = exponent_matrix( b )

        # Thanks to my terrible notation, the elements of b are what are called
        # g_i in the article, while the elements of bb will be the b_i's.
        bb = [ abs(b[i]) ^ (2^(-divisibility(M[i],2))) for i in range(len(b)) ]

        # Computing a combination of bb elements of the form 2 * square.
        MM = exponent_matrix( bb + [2] ).change_ring( GF( 2 ) ) 

        for a in MM.kernel().basis():
            if a[-1] != 0:
                # the vector a[0:-1] gives the coefficients for a combination
                # of the b_i's of the form 2 * square
                
                # Basis elements that actually appear in the combination
                c = [ b[i] for i in range(len(a[0:-1])) if a[i] != 0 ]

                # Return the parameters, changing only the ones for the element
                # of highest divisibility that appears in the combination.
                ret = []
                div_max = -1
                ind_max = -1
                for i in range(len(b)):
                    ret.append( (divisibility(M[i],2), 1-max(0,sgn(b[i]))) )
                    if a[i] != 0 and ret[i][0] > div_max:
                        div_max = ret[i][0]
                        ind_max = i
                d1, h1 = ret[ind_max]
                if d1 == 1:
                    h1 = 1 - h1
                elif d1 == 0:
                    h1 = 2
                ret[ind_max] = ( d1+1, h1 )

                return ret

        return parameters_Q( gb, 2 )

# Uses Theorem 18 to compute the degree of Kummer extensions.
def compute_vl( p, n, m, r ):
    h = [ x[1] for x in p ]
    ni = [ min( n, x[0] ) for x in p ]
    M = max( m, max( [ h[i] + ni[i] for i in range( len( p ) ) ] ) )
    
    return M - m + r*n - sum( ni )

# Computes a basis for G from a set of generators.
# Returns a pair (B,torsion) where B is a list of rational numbers and torsion
# is true if -1 is in G and false otherwise.
def generators_to_basis( G ):
    (BM,BM_primes) = exponent_matrix_with_sign_and_primes( G )
    BM = BM.echelon_form()
    BM_primes.append(-1)

    #B = []
    #torsion = False

    #for r in BM.rows():
    #    gr = product( [ BM_primes[i]^r[i] for i in range(len(r)) ] )
    #    if gr == -1:
    #        torsion = True
    #        break
    #    elif gr == 1:
    #        break
    #   else:
    #        B.append(gr)

    #return (B,torsion)

    B = [ prod([BM_primes[i]^r[i] for i in range(len(r))]) for r in BM.rows() ]

    return ( [ x for x in B if abs(x) != 1 ], -1 in B )


# Given any basis b of a group G computes an l-good basis for G. This is done
# using the algorithm outlined in the proof of Theorem 14 of (Debry-Perucca).
def make_good_basis( b, l ):
    M = exponent_matrix( b )
    #d = []
    #B = []
    #for i in range(len(b)):
    #    di = divisibility( M[i], l )
    #    d.append( di )
    #    B.append( abs(b[i])^(1/(l^di)) )
    d = [ divisibility(x,l) for x in M ]
    B = [ abs(b[i])^(1/(l^d[i])) for i in range(len(b)) ]

    # Computes the coeffiecients of a linear combination of the rows of M
    # that is zero modulo l. These coefficients are elements of F_l.
    coeffs = find_combination( exponent_matrix( B ), l )

    while coeffs != []:

        # Computes which basis element (with non-zero coefficient in the linear
        # combination above) has maximal divisibility.
        maxi = -1
        maxd = -1
        for i in range(len(d)):
            if d[i] > maxd and coeffs[i] != 0:
                maxd = d[i]
                maxi = i

        x = [ (a/coeffs[maxi]).lift() for a in coeffs ] # Now a vector of ints

        #new_elt = 1
        #for i in range(len(d)):
        #    new_elt *= b[i]^( x[i] * l^(d[maxi]-d[i]) )
        new_elt = prod([ b[i]^(x[i]*l^(d[maxi]-d[i])) for i in range(len(d)) ])
        
        b[maxi] = new_elt
        M = exponent_matrix( b )
        d[maxi] = divisibility( M[maxi], l )
        B[maxi] = abs(b[maxi])^(1/(l^d[maxi]))
        
        coeffs = find_combination( exponent_matrix( B ), l )

    #GB = [[]]
    #for i in range(len(d)):
    #    while( len(GB) <= d[i] ):
    #        GB.append([])
    #    GB[d[i]].append(b[i])
    #return GB

    return [[b[i] for i in range(len(b)) if d[i]==j] for j in range(max(d)+1)]

# Takes a good basis B and adjusts the sign of the elements so that there is at
# most one negative generator (of positive divisibility). The input is a good
# basis in the format returned by make_good_basis.
# Returns a pair (B,d), where B is the updated basis and d is the divisibility
# parameter of the only negative element remained.
# The sign of the d=0 elements is just ignored in the other steps of the
# algorithm, so we keep them negative.
def adjust_sign( B ):
    neg = 0
    dret = -1
    for d in range( len(B)-1, 0, -1 ):
        for i in range(len(B[d])):
            if B[d][i] < 0:
                if neg == 0:
                    neg = B[d][i]
                    dret = d
                else:
                    B[d][i] *= neg
    return (B,dret)

# Given the exponent matrix M of a list of rational numbers B, returns the
# coefficients of a linear combination that is weakly l-divisible, or [] if
# the B[i] are strongly l-independent.
def find_combination( M, l ):
    M = M.change_ring( GF( l ) )
    if M.rank() != min( M.dimensions() ):
        return M.kernel().basis()[0]
    else:
        return []

# A rational number must be given as a list of exponents of primes in its
# factorization.
# Returns the minimal l-valuation of the exponents.
def divisibility( A, l ):
    if len(A) == 0:
        print "Warning: computing the divisibility of a torsion element.",
        print "Returning +Infinity."
        return +Infinity
    return min( [ valuation( x, l ) for x in A ] )

# For a given set of non-zero rationals B, computes the "exponent matrix"
def exponent_matrix( B ):
    prime_list = set()
    for g in B:
        prime_list |= set( prime_factors( g ) )
    prime_list = list( prime_list )
    np = len( prime_list )
    rows = []
    for g in B:
        rowg = [0] * np
        for f in list( factor( g ) ):
            for i in range( np ):
                if f[0] == prime_list[i]:
                    rowg[i] = f[1]
        rows.append( rowg )
    return matrix( rows )

# Computing the exponent matrix, but keeping an extra column for the signs.
# Returns a pair (M,L) where M is the modified exponent matrix and L is the
# list of primes appearing in the factorization.
def exponent_matrix_with_sign_and_primes( B ): 
    #prime_list = set()
    #for g in B:
    #    prime_list |= set( prime_factors( g ) )
    #prime_list = list( prime_list )

    prime_list = list({ x for a in [prime_factors(g) for g in B] for x in a })
    np = len( prime_list )

    rows = []
    for g in B:
        rowg = [0] * np
        for f in list( factor( g ) ):
            for i in range( np ):
                if f[0] == prime_list[i]:
                    rowg[i] = f[1]
        rowg.append( 1 - max(0,sgn(g)) ) 
        rows.append( rowg )
    return ( matrix( rows ), prime_list )

# This is a wrapper function for total_kummer_failure( G, True ), see below.
def TotalKummerFailure( G ):
    total_kummer_failure( G, True )

# Input: any set of generators for a subgroup G of Q*.
# If output=False, returns a 4-uple (t,MM,NN,D):
# - t is a pair, where t[0] is the rank of G and t[1] is either True (if G has
#   torsion) or False (is it does not).
# - MM is the pair (M0,divisors(M0))
# - NN is the pair (N0,divisors(N0))
# - D is a table F, where F[j][i] is the ration between phi(m)n^r and the
#   degree of Q_{m,n} (i.e., the Kummer failure at m,n, where m is the i-th
#   divisor of M0 and n is the j-th divisor of N0 (in the computed list))
#   computed for a torsion-free part of G.
# If output is True, outputs this data in a human-readable way and does not
# return any value.
def total_kummer_failure( G, output ):

    B, torsion = generators_to_basis( G )
    r = len(B) # Rank of G

    if r == 0:
        print "G is torsion. The extension is cyclotomic. Stopping."
        return False

    # Compute l-adic data (straightforward)
    ( bad_primes, l_adic_failure_table ) = total_l_adic_failure( B )

    # Compute adelic data.
    (GB,d) = adjust_sign( make_good_basis( B, 2 ) )
    adelic_failure_table = adelic_failure_gb( GB, d )
    
    # Computing the bounds M0 and N0
    #N0 = 1
    #for i in range(len( bad_primes )):
    #    N0 *= bad_primes[i] ^ len( l_adic_failure_table[i][-1][0] )
    N0 = prod( [ bad_primes[i] ^ len( l_adic_failure_table[i][-1][0] ) \
            for i in range(len(bad_primes)) ] )
    # Extra factors of 2 may come from the adelic failure
    N0 = lcm( N0, 2^len( adelic_failure_table ) )
    divs_N0 = divisors(N0)

    # greatest M appearing in the adelic failure table
    M0 = adelic_failure_table[-1][-1][0]
    divs_M0 = divisors(M0)

    # Failure Table
    FT = [ [ 1 for d1 in divisors(M0) ] for d2 in divisors(N0) ]

    # Takes the adelic failure from the the relative table
    for i in range(1,len(adelic_failure_table)+1):
        for pp in adelic_failure_table[i-1]:
            # Runs through all divisors of M0 and N0 that may have this
            # failure (the table is not "complete").
            for l in range(len(divs_M0)):
                for j in range(len(divs_N0)):
                    dM = divs_M0[l]
                    dN = divs_N0[j]
                    if dN%(2^i)==0:
                        if dN%(2^(i+1))!=0 or i==len(adelic_failure_table):
                            if dM % pp[0] == 0:  
                                FT[j][l] = lcm( FT[j][l], pp[1] )

    # Adding l-adic failure to the table
    for i in range( len( bad_primes ) ):
        l = bad_primes[i]
        for j in range(len(divs_N0)):
            dN = divs_N0[j]
            fl = l_adic_failure_from_data(B,l,l_adic_failure_table[i],dN,dN)
            for h in range(len(divs_M0)):
                FT[j][h] *= fl

    ret = ( ( r, torsion ), ( M0, divs_M0 ), ( N0, divs_N0 ), FT )

    if output:
        print_total_table( ret )
        # Uncomment following line for case list description.
        #print_case_list( ret )
        return
    else:
        return ret

# For the torsion tables, recall that when -1 is in G, the failure is defined
# as the ration between 2^eN^r and the degree of Q_{M,N} over Q_M, where e=1
# if N is even and e=0 otherwise.

# Makes the failure table for the torsion case when M/N is even. In this case,
# an entry of the table is doubled if the corresponding value of N (actually,
# of gcd(N,N0) ) is even, and is kept the same otherwise.
# The expected degree (over Q) 2^e * phi(M) * N^r, where e=1 if N is even and
# e=0 otherwise.
def torsion_table_even( data ):

    ( ( r, torsion ), ( M0, divs_M0 ), ( N0, divs_N0 ), FT ) = data

    new_FT = [ [ 1 for d1 in divs_M0 ] for d2 in divs_N0 ]
    for i in range(len(divs_N0)):
        for j in range(len(divs_M0)):
            if divs_N0[i] % 2 == 0:
                new_FT[i][j] = 2 * FT[i][j]

    return new_FT

# Makes the failure table for the torsion case when M/N is odd. In this case
# the entry at (M,N) is taken from the torsion-free entry at (2M,N).
# In other words, the expected degree (over Q) 2^e * phi(M) * N^r, where e=1 if
# N is even and e=0 otherwise.
def torsion_table_odd( data ):

    ( ( r, torsion ), ( M0, divs_M0 ), ( N0, divs_N0 ), FT ) = data
    
    new_FT = [ [ 1 for d1 in divs_M0 ] for d2 in divs_N0 ]
    new_data = ( ( r, False ), ( M0, divs_M0 ), ( N0, divs_N0 ), FT )
    for i in range(len(divs_N0)):
        for j in range(len(divs_M0)):
            dN = divs_N0[i]
            dM = divs_M0[j]
            # The following lines just copy the failure from (2M,N) in the 
            # torsion-free case. It is easier to write it like this, although
            # it is not necessary in theory to compute the degree.
            exp_deg = euler_phi(2*dM) * dN^r
            deg = kummer_degree_from_total_table( 2*dM, dN, new_data ) 
            new_FT[i][j] = exp_deg / deg
    
    return new_FT

def print_total_table( data ):

    ( ( r, torsion ), ( M0, divs_M0 ), ( N0, divs_N0 ), FT ) = data
    
    print "M_0 =", M0
    print "N_0 =", N0
    print ""
    print "The following table shows the total failure of Kummer", 
    if torsion:
        print "degrees in case the quotient M/N is EVEN."
    else:
        print "degrees."
    print "The degree of the Kummer extension (M,N) is e / f, where",
    if torsion:
        print "e = phi(M)*N^rank(G) if N is odd and e = 2*phi(M)*N^rank(G)",
        print "if N is even",
    else:
        print "e = phi(M)*N^rank(G)",
    print "and f is the entry of the table below at the row labelled with",
    print "gcd(N,N0) and the column labelled with gcd(M,M0)."
    print ""

    if torsion:
        FT1 = torsion_table_even( data )
    else:
        FT1 = FT

    tt = [ ["","|"] + divs_M0 ]
    tt.append( "-" * (len(divs_M0)+2) )
    for i in range(len(divs_N0)):
        tt.append( [ divs_N0[i] ] + ["|"]  + FT1[i] )
    print table(tt)
    print ""

    if torsion:
        print "The following table shows the total failure of Kummer degrees",
        print "in case the quotient M/N is ODD and is read as the previous one."
        print ""

        # A good strategy is the following:
        #   A little translation exercise: the failure at (M,N) in the torsion
        #   case is either the same as that for (2M,N) in the torsion-free case
        #   (if M is even) or its double (if M is odd).
        # However, due to problems in reading the table for bigger M, it is
        # easier to just compute the degree every time, and then deduce the
        # failure. This is not too inefficient, since we can use the data that
        # we have already computed via kummer_degree_from_total_table.
        new_FT = torsion_table_odd( data )
        # Printing the new table
        tt = [ ["","|"] + divs_M0 ]
        tt.append( "-" * (len(divs_M0)+2) )
        for i in range(len(divs_N0)):
            tt.append( [ divs_N0[i] ] + ["|"]  + new_FT[i] )
        print table(tt)
        print ""

def print_case_list( data ):

    ( ( r, torsion ), ( M0, divs_M0 ), ( N0, divs_N0 ), FT ) = data
    FT_odd = torsion_table_odd( data )

    if torsion:
        FT1 = torsion_table_even( data )
        pf = sorted(list({ x for row in FT_odd for x in row }))
    else:
        FT1 = FT
        pf = sorted(list({ x for row in FT1 for x in row }))

    for f in pf:
        print "Failure is", f, "if",
        if torsion:
            print "M/N is EVEN and",
        print "(gcd(M,M0),gcd(N,N0)) is one of the following:"
        print [ (divs_M0[j], divs_N0[i]) \
                for i in range(len(divs_N0)) for j in range(len(divs_M0)) \
                if FT1[i][j] == f ]

        if torsion:
            print "or if M/N is ODD and (gcd(M,M0)),gcd(N,N0)) is one of the",
            print "following:"
            print [ (divs_M0[j], divs_N0[i]) \
                    for i in range(len(divs_N0)) for j in range(len(divs_M0)) \
                    if FT_odd[i][j] == f ]

        print ""

# Extracts a specific value of failure from the total table.
def kummer_failure_from_total_table( M, N, data ):
    ( ( r, torsion ), ( M0, divs_M0 ), ( N0, divs_N0 ), FT ) = data

    if torsion:
        if (M/N) % 2 == 0:
            FT1 = torsion_table_even( data )
        else:
            FT1 = torsion_table_odd( data )
    else:
        FT1 = FT

    return FT1[divs_N0.index( gcd( N, N0 ) )][divs_M0.index( gcd( M, M0 ) )]

# Computes the degree of the Kummer extension (M,N), by taking as input the
# table computed by TotalKummerFailure.
def kummer_degree_from_total_table( M, N, data ):
    
    ( ( r, torsion ), ( M0, divs_M0 ), ( N0, divs_N0 ), FT ) = data

    exp_deg = euler_phi(M) * N^r
    if torsion and N % 2 == 0:
        exp_deg *= 2
    return exp_deg / kummer_failure_from_total_table( M, N, data )

# Given a set of generators for a finitely generated subgroup G of the
# multiplicative group of Q, returns the degree of Q_{M,N} over Q.
# M must be a multiple of N.
def KummerDegree( G, M, N ):
    if M % N != 0:
        print "M is not a multiple of N"
        return -1

    data = total_kummer_failure(G,False)
    ((r,torsion),(M0,divs_M0),(N0,divs_N0),FT) = data

    exp_deg = euler_phi(M) * N^r
    
    if torsion and N % 2 == 0:
        exp_deg *= 2
    
    if torsion: 
        if (M/N)%2 == 0:
            failure = torsion_table_even( data )
        else:
            failure = torsion_table_odd( data )
    else:
        failure = FT

    return exp_deg/failure[divs_N0.index(gcd(N,N0))][divs_M0.index(gcd(M,M0))]
