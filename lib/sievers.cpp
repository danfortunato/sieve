#include "sievers.h"
#include <math.h>
#include <stdlib.h>
#include <algorithm>
#include <numeric>
using namespace std;

template <typename T> mint sgn(T val)
{
	return (T(0) < val) - (val < T(0));
}

mint mod(mint a, mint b)
{
	mint res = a % b;
	if (res < 0)
	{
		res += b;
	}
	return res;
}

mvector segmentedPrimeQSieve(mint lo, mint hi, mint delta, mvector primes)
{
	mint i, k, len, p, sqrt_hi, st;
	mvector S (hi-lo+1, 1);

	sqrt_hi = round(sqrt(hi));

	len = primes.size();
	for (i = 0; i < len; i++)
	{
		p = primes[i];

		if (p > sqrt_hi)
		{
			break;
		}

		st = lo + mod(-lo, p);
		// st = lo + (-lo % p) + p;

		if (st > hi)
		{
			continue;
		}

		if (st == p)
		{
			st += p;
		}

		for (k = st-lo+1; k <= hi-lo+1; k += p)
		{
			S[k-1] = 0;
		}
	}

	if (lo <= 1 && 1 <= hi)
	{
		S[2-lo-1] = 0;
	}

	if (delta != 1)
	{
		for (i = 0; i < S.size(); i++)
		{
			if ((i % delta) != 0)
			{
				S.erase(S.begin()+i);
			}
		}
	}

	return S;
}

mvector segmentedMoebiusMuSieve(mint lo, mint hi, mint delta, mvector primes)
{
	mint i, k, len, p, p2, sqrt_hi, st, Sk;
	mvector S (hi-lo+1, 1);

	sqrt_hi = round(sqrt(hi));

	len = primes.size();
	for (i = 0; i < len; i++)
	{
		p = primes[i];
		p2 = pow(p, 2);

		if (p > sqrt_hi)
		{
			break;
		}

		st = lo + (-lo % p) + p;
		if (st > hi)
		{
			continue;
		}

		for (k = st-lo+1; k <= hi-lo+1; k += p)
		{
			S[k-1] *= -p;
		}

		st = lo + (-lo % p2) + p2;
		if (st > hi)
		{
			continue;
		}

		for (k = st-lo+1; k <= hi-lo+1; k += p2)
		{
			S[k-1] = 0;
		}
	}

	len = S.size();
	for (k = 0; k < len; k++)
	{
		Sk = S[k];
		if (labs(Sk) < k + lo)
		{
			S[k] = -1*sgn(Sk);
		}
		S[k] = sgn(S[k]);
	}

	if (delta != 1)
	{
		for (i = 0; i < len; i++)
		{
			if ((i % delta) != 0)
			{
				S.erase(S.begin()+i);
			}
		}
	}

	return S;
}

mvector segmentedPrimeSieve(mint l, mint hi, mint delta, mvector primes)
{
	mint lo, sqrt_hi, p, st, i, k, len;
	lo = max(l, (mint)2);
	sqrt_hi = round(sqrt(hi));
	mvector S (hi-lo+1);
	len = S.size();
	for (i = 0; i < len; i++)
	{
		S[i] = lo + i;
	}

	len = primes.size();
	for (i = 0; i < len; i++)
	{
		p = primes[i];

		if (p > sqrt_hi)
		{
			break;
		}

		st = lo + mod(-lo, p);

		if (st > hi)
		{
			continue;
		}

		if (st == p)
		{
			st += p;
		}

		for (k = st-lo+1; k <= hi-lo+1; k += p)
		{
			S[k-1] = 0;
		}
	}

	if (delta == 1)
	{
		len = S.size();
		mvector S_positive;
		for (i = 0; i < len; i++)
		{
			if (S[i] > 0)
			{
				S_positive.push_back(S[i]);
			}
		}
		return S_positive;
	}
	else
	{
		for (i = 0; i < S.size(); i++)
		{
			if ((i % delta) != 0)
			{
				S.erase(S.begin()+i);
			}
		}
		return S;
	}
}

mvector segmentedLeastPrimeFactorSieve(mint lo, mint hi, mint delta, mvector primes)
{
	mint p, st, i, k, len;
	mvector S (hi-lo+1);
	len = S.size();
	for (i = 0; i < len; i++)
	{
		S[i] = lo + i;
	}

	len = primes.size();
	for (i = len-1; i >= 0; i--)
	{
		p = primes[i];

		st = lo + mod(-lo, p);

		if (st > hi)
		{
			continue;
		}

		if (st == p)
		{
			st += p;
		}

		for (k = st-lo+1; k <= hi-lo+1; k += p)
		{
			S[k-1] = p;
		}
	}

	if (delta != 1)
	{
		for (i = 0; i < len; i++)
		{
			if ((i % delta) != 0)
			{
				S.erase(S.begin()+i);
			}
		}
	}

	return S;
}
