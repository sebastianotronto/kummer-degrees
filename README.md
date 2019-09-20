# Kummer Degrees
A SageMath script that computes the degrees of Kummer Extensions of the
rational numbers.

It contains the following useful functions:

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

## KummerDegree( G, M, N )

Returns the degree of the Kummer extension Q_{M,N}. Again, G is given simply as a list of generators and it may contain torsion.

Example:
```
sage: KummerDegree([-36,12,-1],120,24)
4608
```
