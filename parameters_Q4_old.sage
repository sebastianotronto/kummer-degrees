# Computes the l-divisibility parameters of G over Q4, given a good basis gb
# over Q for G. Returns a list of pairs (di,hi).
# If l is odd it just uses the good basis given to compute the parameters.
def parameters_Q4( gb, l ):
    # Converts from "good basis format" to simple list
    b = []
    for x in gb:
        b += x
    ret = []
    
    if l != 2:
        for i in range( len( gb ) ):
            for j in gb[i]:
                ret.append( (i,0) )
        return ret
    else:
        R.<y> = PolynomialRing( QQ )
        pol = R(y^2+1)
        Q4.<eye> = NumberField( pol ) # I already use i for other things

        # Factorize basis elements over Q4 and so on.
        d = []
        B = []
        h = []
        ideals_list = set()
        M = [] # Exponent matrix of the Bi's

        # Pre-process to find all ideals appearing in the factorization and fix
        # a chosen generator for each of them. This is important in order to
        # compute the "sign" (h-parameter) of an element with respect to it Bi.
        for g in b:
            factorization_list = list( Q4.ideal(g).factor() )
            ideals_list |= set( [ x[0] for x in factorization_list ] )
        ideals_list = list( ideals_list )
        # Chooses a generator of each principal ideal in the list
        irreducibles_list = [ J.gens_reduced()[0] for J in ideals_list ]

        # Compute the Q4-parameters of the given basis b. Also computes the
        # exponent matrix of the Bi's 
        for g in b:
            factorization_list = list( Q4.ideal(g).factor() )
            exps = [ x[1] for x in factorization_list ]
            d.append( divisibility( exps, l ) )
            Bg = 1
            for j in range(len(factorization_list)):
                a = 0
                for i in range( len( ideals_list ) ):
                    if ideals_list[i] == factorization_list[j][0]:
                        a = irreducibles_list[i]
                        break
                Bg *= a ^ (exps[j]/(l^d[-1]))
            B.append(Bg)
            u = g / (Bg^(l^d[-1]))
            if not u.is_unit():
                print "Error: g is not the right power of the computed Bg."
                print "g:", g, ", Bg:", Bg, ", exponent:", l^d[-1]
            if u == 1:
                h.append( 0 )
            elif u == -1:
                h.append( 1 )
            else:
                h.append( 2 ) 

        # Make the exponent matrix M (for now as a list of rows)
        for g in B:
            row = [0] * len(ideals_list)
            for i in range(len(ideals_list)):
                I = ideals_list[i]
                ee = 1
                while (I^ee).divides(g):
                    ee += 1
                row[i] = ee-1
            M.append(row)

        # If the Bi's are not strongly independent, apply the algorithm (only
        # once) to produce a new basis. The new basis has maximal parameters.
        coeffs = find_combination( matrix(M), l )
        if coeffs != []:

            maxi = -1
            maxd = -1
            for i in range(len(d)):
                if d[i] > maxd and coeffs[i] != 0:
                    maxd = d[i]
                    maxi = i

            x = [(a/coeffs[maxi]).lift() for a in coeffs] # Now a vector of int

            new_element = 1
            for i in range(len(d)):
                new_element *= b[i]^( x[i] * l^(d[maxi]-d[i]) )
        
            b[maxi] = new_element

            # Compute new B, d and so on.
            factorization_list = list( Q4.ideal(b[maxi]).factor() )
            exps = [ x[1] for x in factorization_list ]
            d[maxi] = divisibility( exps, l )
            Bg = 1

            for j in range(len(factorization_list)):
                a = 0
                for i in range( len( ideals_list ) ):
                    if ideals_list[i] == factorization_list[j][0]:
                        a = irreducibles_list[i]
                        break
                Bg *= a ^ (exps[j]/(l^d[maxi]))
            B[maxi] = Bg
            M[maxi] = [ x[1] for x in list( Q4.ideal(Bg).factor() ) ]
            u = b[maxi] / (Bg^(l^d[maxi]))
            if not u.is_unit():
                print "Error: new element is not the right power of B."
                print "New el.:", b[maxi], ", B:", Bg, ", exponent:", l^d[maxi]
            if u == 1:
                h[maxi] = 0
            elif u == -1:
                h[maxi] = 1
            else:
                h[maxi] = 2 
            
        return [(d[i],h[i]) for i in range(len(d))]


