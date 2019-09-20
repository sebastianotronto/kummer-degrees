# Kummer Degrees
A one-file SageMath script that computes the degrees of Kummer Extensions of
the rational numbers. In order to use the functions KummerDegree and
TotalKummerFailure (described below), simply download the file
kummer_degree.sage and include it in your project, for example with
attach("kummer_degree.sage").

A Kummer Extension of Q is a field extension of the form Q_{M,N}:=
Q(\zeta_M,G^{1/N}), where:
* M and N are integers with N dividing M;
* \zeta_M is a root of unity of order M;
* G is a finitely generated subgroup of the multiplicative group of Q;
* G^{1/N} is the set of all elements x of an algebraic closure of Q such that
x^n belongs to G.

The main importance of this script is to show that, for a fixed group G as
above, one can compute in a finite time a finite-case-distinction formula
that computes the degrees [Q_{M,N}:Q] of such extensions when M and N vary.
A preprint by A. Perucca, P. Sgobba and S. Tronto that explains how this is
possible can be found in the docs folder.

I have not computed accurately the complexity of the code. However, I can
say the following:
* The complexity is exponential in the rank r of the group.
* The script can become slow if the generators of the group G are n-th powers
for very high n.
* The generators given are factored as product of prime powers, so very large
generators can slow the script as well.
* The code is very fast for groups of small rank (e.g. up to 5) and generated
by elements of magnitude 10^6; higher ranks are feasible as well with smaller
generators.


## KummerDegree( G, M, N )

Returns the degree of the Kummer extension Q_{M,N}. Again, G is given simply as a list of generators and it may contain torsion.

Example:
```
sage: KummerDegree([-36,12,-1],120,24)
4608
```

## TotalKummerFailure( G )

Outputs the description of the failure of maximality for all possible values of M and N. Here G is given as a list of generators (not necessarily a basis). G can also contain torsion. If G = <-1>, the program stops immediately.

Example:

```

sage: TotalKummerFailure([-36,12,-1])
M_0 = 24
N_0 = 8

The following table shows the total failure of Kummer degrees in case the quotient M/N is EVEN.
The degree of the Kummer extension (M,N) is e / f, where e = phi(M)*N^rank(G) if N is odd and e = 2*phi(M)*N^rank(G) if N is even and f is the entry of the table below at the row labelled with gcd(N,N0) and the column labelled with gcd(M,M0).

      |   1   2   3   4   6   8   12   24
  -   -   -   -   -   -   -   -   -    -
  1   |   1   1   1   1   1   1   1    1
  2   |   4   4   4   4   4   4   8    8
  4   |   4   4   4   4   4   8   8    16
  8   |   8   8   8   8   8   8   8    16

The following table shows the total failure of Kummer degrees if the quotient M/N is ODD and is read as the previous one.

      |   1   2   3   4   6   8   12   24
  -   -   -   -   -   -   -   -   -    -
  1   |   1   1   1   1   1   1   1    1
  2   |   2   2   2   2   4   2   4    4
  4   |   2   2   2   4   4   4   8    8
  8   |   4   4   4   4   4   4   8    8

```


