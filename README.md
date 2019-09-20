# Kummer Degrees
A one-file SageMath script to compute the degrees of Kummer Extensions of
the rational numbers. In order to use the functions KummerDegree and
TotalKummerFailure (described below), simply download the file
kummer_degree.sage and include it in your SageMath session/project,
for example with
```
attach("kummer_degree.sage")
```

A Kummer Extension of Q is a field extension of the form Q_{M,N}:=
Q(\zeta_M,G^{1/N}), where:
* M and N are integers with N dividing M;
* \zeta_M is a root of unity of order M;
* G is a finitely generated subgroup of the multiplicative group Q* of Q;
* G^{1/N} is the set of all elements x of an algebraic closure of Q such that
x^n belongs to G.

In other words, it is a number field generated by finitely many elements of
the form a^{1/n} and "at least sufficiently many" roots of unity to make
this field Galois over Q.

The main importance of this script is to show that, for a fixed group G as
above, one can compute in a finite time a finite-case-distinction formula
that computes the degrees of such extensions when M and N vary.
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
* The complexity of the calculation of a call of KummerDegree(G,M,N) does not
depend on M and N.

Moreover, the results for each group G are cached, so that subsequent
computation of degrees for the same group G only require constant time
(and are very fast).


## KummerDegree( G, M, N )

Returns the degree of the Kummer extension Q_{M,N}=Q(\zeta_M,G^{1/N}) over Q.

INPUT:
* G - a list of generators of the group G
* M - a positive integer
* N - a positive divisor of N

OUTPUT:
The degree of the Kummer Extensions Q_{M,N}=Q(\zeta_M,G^{1/N}) over Q.

EXAMPLES:
```
sage: KummerDegree([5],10,2)
4
sage: KummerDegree([-36,12,-1],120,24)
4608
sage: KummerDegree([144,27,49/81,-1/125,121/13],36*10^6,36*10^6)
1007769600000000000000000000000000000000000
```

## TotalKummerFailure( G )

Outputs the description of the failure of maximality for all possible values
of M and N.

INPUT:
G - a list of generators for the group G

OUPUT:
The first part of the output consist of two positive integers M_0 and N_0.
N_0 is always a divisor of M_0.

The second part of the output can be either one or two tables, depending on
the group G. In case -1 is not an element of G, there is only one table,
otherwise two.

In case -1 does not belong to G:
The rows of the table(s) are labelled with divisors of N_0, while the columns
with divisors of M_0. The total failure of maximality of the Kummer Extension
Q_{M,N}, i.e. the ratio between phi(M)*N^rank(G) and the degree of Q_{M,N}
over Q, is given by the (i,j)-th entry of the table for i=gcd(N,N_0) and
j=gcd(M,M_0).

In case -1 belongs to G, we need to distinguish two cases, depending on the
parity of M/N. The two tables are similar to the case described
above, and can be seen in the example below.

The output includes an explanation of the tables and how to read them to
deduce the actual degrees (that can be computed with KummerDegree).

EXAMPLES:

```
sage: TotalKummerFailure([-36,12])
M_0 = 24
N_0 = 8

The following table shows the total failure of Kummer degrees.
The degree of the Kummer extension (M,N) is e / f, where e = phi(M)*N^rank(G)
and f is the entry of the table below at the row labelled with gcd(N,N0) and
the column labelled with gcd(M,M0).

      |   1   2   3   4   6   8   12   24
  -   -   -   -   -   -   -   -   -    -
  1   |   1   1   1   1   1   1   1    1
  2   |   1   1   1   2   2   2   4    4
  4   |   4   4   4   4   4   4   8    8
  8   |   4   4   4   4   4   4   4    8

```

```
sage: TotalKummerFailure([-36,12,-1])
M_0 = 24
N_0 = 8

The following table shows the total failure of Kummer degrees in case the
quotient M/N is EVEN.
The degree of the Kummer extension (M,N) is e / f, where e = phi(M)*N^rank(G)
if N is odd and e = 2*phi(M)*N^rank(G) if N is even and f is the entry of the
table below at the row labelled with gcd(N,N0) and the column labelled with
gcd(M,M0).

      |   1   2   3   4   6   8   12   24
  -   -   -   -   -   -   -   -   -    -
  1   |   1   1   1   1   1   1   1    1
  2   |   4   4   4   4   4   4   8    8
  4   |   4   4   4   4   4   8   8    16
  8   |   8   8   8   8   8   8   8    16

The following table shows the total failure of Kummer degrees if the quotient
M/N is ODD and is read as the previous one.

      |   1   2   3   4   6   8   12   24
  -   -   -   -   -   -   -   -   -    -
  1   |   1   1   1   1   1   1   1    1
  2   |   2   2   2   2   4   2   4    4
  4   |   2   2   2   4   4   4   8    8
  8   |   4   4   4   4   4   4   8    8

```

Uncommenting the line of code:
```
print_case_list( ret )
```
inside the function total_kummer_failure makes the script output the
description of the total failure as a finite list of cases, as below:

```

sage: TotalKummerFailure([25])
M_0 = 40
N_0 = 8

The following table shows the total failure of Kummer degrees.
The degree of the Kummer extension (M,N) is e / f, where e = phi(M)*N^rank(G)
and f is the entry of the table below at the row labelled with gcd(N,N0) and
the column labelled with gcd(M,M0).

      |   1   2   4   5   8   10   20   40
  -   -   -   -   -   -   -   -    -    -
  1   |   1   1   1   1   1   1    1    1
  2   |   2   2   2   2   2   2    2    2
  4   |   2   2   2   2   2   2    4    4
  8   |   2   2   2   2   2   2    2    4

Failure is 1 if (gcd(M,M0),gcd(N,N0)) is one of the following:
[(1, 1), (2, 1), (4, 1), (5, 1), (8, 1), (10, 1), (20, 1), (40, 1)]

Failure is 2 if (gcd(M,M0),gcd(N,N0)) is one of the following:
[(1, 2), (2, 2), (4, 2), (5, 2), (8, 2), (10, 2), (20, 2), (40, 2), (1, 4), (2, 4), (4, 4), (5, 4), (8, 4), (10, 4), (1, 8), (2, 8), (4, 8), (5, 8), (8, 8), (10, 8), (20, 8)]

Failure is 4 if (gcd(M,M0),gcd(N,N0)) is one of the following:
[(20, 4), (40, 4), (40, 8)]
```
