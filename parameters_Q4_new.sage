# Returns the l-dvisibility parameters of G over Q, given a good basis gb of G,
# as a list of pairs (di,hi).
def parameters_Q( gb, l ):
    ret = []
    for i in range( len( gb ) ):
        for j in gb[i]:
            ret.append( (i,0) )
    return ret

# Computes the l-divisibility parameters of G over Q4, given a good basis gb
# over Q for G. Returns a list of pairs (di,hi).
# If l is odd it just uses the good basis given to compute the parameters.
# If l=2, it uses the results of PST-2.
def parameters_Q4_new( gb, l ):
    if l != 2:
        return parameters_Q( gb, l )
    else:
        # Converts from "good basis format" to simple list
        b = []
        for x in gb:
            b += x
    
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

                # Return the parameters, changing only the ones fo the element
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

