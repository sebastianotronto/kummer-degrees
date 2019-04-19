# Kummer Degrees
A SageMath script that computes the degrees of Kummer Extensions of the rational numbers.
It contains the following useful functions:

## TotalKummerFailure( G )

Outputs the description of the failure of maximality for all possible values of M and N. Here G is given as a list of generators (not necessarily a basis). G can also contain torsion. If G = <-1>, the program stops immediately.

Example:

```
sage: TotalKummerFailure([-36,12,-1])
output:
M_0 = 24
N_0 = 8

The following table shows the total failure of Kummer degrees in
 case the quotient M/N is EVEN.
Columns correspond to values of M, rows to values of N

The degree of the Kummer extension (M,N) can be extracted by taking
the value f (failure) of the entry at (gcd(N,N0),gcd(M,M0)) and
simply computing ed(M,N) / f, where ed(M,N) is the expected degree
of the Kummer extension.
In this case (-1 is in G), we have ed(M,N) = 2^e*phi(M)*N^r,
where e=1 if N is even and e=0 if N is odd.
where r is the rank of G.

      |   1   2   3   4   6   8    12   24
  -   -   -   -   -   -   -   -    -    -
  1   |   1   1   1   1   1   1    1    1
  2   |   4   4   4   4   4   4    8    8
  4   |   4   4   4   4   4   8    8    16
  8   |   8   8   8   8   8   16   16   32

The following table shows the total failure of Kummer degrees in
case the quotient M/N is ODD.
This table can be read exactly as the first one.

      |   1   2   3   4   6   8   12   24
  -   -   -   -   -   -   -   -   -    -
  1   |   1   1   1   1   1   1   1    1
  2   |   2   2   2   2   4   2   4    4
  4   |   2   2   2   4   4   4   8    8
  8   |   4   4   4   8   8   8   16   16

```

## KummerDegree( G, M, N )

Returns the degree of the Kummer extension Q_{M,N}. Again, G is given simply as a list of generators and it may contain torsion.

Example:
```
sage: KummerDegree([-36,12,-1],120,24)
output:
2304
```
