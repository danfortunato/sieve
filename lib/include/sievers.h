#ifndef SIEVERS_H
#define SIEVERS_H

#include "globals.h"
// #include "WolframLibrary.h"
#include <vector>
using namespace std;

mvector segmentedPrimeQSieve(mint lo, mint hi, mint delta, mvector primes);
mvector segmentedMoebiusMuSieve(mint lo, mint hi, mint delta, mvector primes);
mvector segmentedPrimeSieve(mint l, mint hi, mint delta, mvector primes);
mvector segmentedLeastPrimeFactorSieve(mint lo, mint hi, mint delta, mvector primes);

#endif /* SIEVERS_H */
