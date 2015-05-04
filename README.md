# sieve

sieve is a *Mathematica* package and C++ library designed to evaluate arithmetic functions and their sums on a range of integers efficiently.

## Interface

The package exposes the following functions to the user:

**Arithmetic functions over a range**

- `PrimesInRange`
- `PrimeTable`
- `PrimeQTable`
- `PrimePowerQTable`
- `MoebiusMuTable`
- `LeastPrimeFactorsTable`
- `DivisorSigmaTable`
- `EulerPhiTable`
- `SquareFreeInRange`
- `SquareFreeQTable`
- `MangoldtLambdaTable`
- `PrimeNuTable`
- `PrimeOmegaTable`
- `LiouvilleLambdaTable`

**Summatory functions**

- `MertenM`
- `SquareFreePi`
- `DivisorSigmaSum`
- `ChebyshevPsi`
- `ChebyshevTheta`
- `ChebyshevPsiSlow`
- `ChebyshevThetaSlow`
- `Primeπ`

**Miscellaneous**

- `Primorial`
- `LeastPrimeFactor`
- `SquareFree`
- `MeisselMerten`

## Implementation notes

## References

`SquareFreePi`: *Introduction to Analytic Number Theory*, Chapter 3, Tom M. Apostol  
`MertenM`: http://www.researchgate.net/publication/2768786_Computing_the_Summation_of_the_Mbius_Function  
`Primeπ`: http://cr.yp.to/bib/1996/deleglise.pdf & http://www.dtc.umn.edu/~odlyzko/doc/arch/meissel.lehmer.pdf  
`ChebyshevPsi`: http://www.ams.org/journals/mcom/1998-67-224/S0025-5718-98-00977-6/S0025-5718-98-00977-6.pdf  
`DivisorSigmaSum` (yet to be implemented): *Introduction to Analytic Number Theory*, Theorem 3.17, Tom M. Apostol 
