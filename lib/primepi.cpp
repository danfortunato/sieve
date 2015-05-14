#include "primepi.h"
#include "globals.h"
#include "sievers.h"
#include <math.h>
#include <stdlib.h>
#include <vector>
#include <algorithm>
#include <numeric>
using namespace std;

mint getY(mint x);
mint mintegerLength(mint n, mint base);
mvector range(mint n);
mint primepi(mint x);
mvector accumulate(mvector lis);
mvector accumulate_plus(mvector lis, mint init);
mvector primesInRange(mint n);
mint iS3(mint x, mint y, mvector primes, mvector mu);
mvector binaryExponents(mint n, mint w);

mint primepi(mint x)
{
	mint y, i, j, len, p, sqrrt, cbrrt, frthrt, CAP, floorsqrt, ceilsqrt, xy2, pi_y, pi_old, pi_x13;
	mint S0, S1, S3, U, V1, W1, W2, W3, W4, W5;
	mint q, qq, pmin, pmax, w, z, r, s, W1Q, L1, L2, W2Q, P;
	mvector primes, pQ, pismall, mu, primeQ, pis, PP;

	sqrrt  = floor(sqrt(x));
	cbrrt  = floor(cbrt(x));
	frthrt = floor(pow(x, 1/4.));
	y = getY(x);
	CAP = ceil((float)x/(float)y);
	floorsqrt = floor(sqrt((float)x/(float)y));
	ceilsqrt  = ceil(sqrt((float)x/(float)y));
	xy2 = x/(y*y);
	
	time_t t = clock();
	primes = primesInRange(y);
	printf("primesInRange(%li): %f\n", y, difftime(clock(), t)/CLOCKS_PER_SEC);
	
	t = clock();
	pQ = segmentedPrimeQSieve(1, y, 1, primes);
	printf("segmentedPrimeQSieve(1, %li): %f\n", y, difftime(clock(), t)/CLOCKS_PER_SEC);

	pismall = accumulate(pQ);

	pi_y   = pismall[y-1];
	pi_old = pismall[y-1];
	pi_x13 = pismall[cbrrt-1];

	t = clock();
	mu = segmentedMoebiusMuSieve(1, y, 1, primes);
	printf("segmentedMoebiusMuSieve(1, %li): %f\n", y, difftime(clock(), t)/CLOCKS_PER_SEC);

	/************************************
	 ** All PrimePi[z] for 1 <= z <= y **
	 ************************************/

	// In this section we compute:
	//   - all of S0, S1, U, V1, W3, W4, W5
	//   - part of W2

	/*** S0 ***/
	t = clock();
	S0 = 0;
	len = mu.size();
	for (i = 0; i < len; i++)
	{
		S0 += mu[i] * (x/(i+1));
	}
	printf("S0: %f\n", difftime(clock(), t)/CLOCKS_PER_SEC);

	/*** S1 ***/
	t = clock();
	S1 = (pi_y - pi_x13)*(pi_y - pi_x13 - 1)/2;
	printf("S1: %f\n", difftime(clock(), t)/CLOCKS_PER_SEC);

	/*** U ***/
	t = clock();
	U = 0;
	for (i = pismall[floorsqrt-1]; i < pismall[cbrrt-1]; i++)
	{
		U += pi_y - pismall[x/(primes[i]*primes[i])-1];
	}
	printf("U: %f\n", difftime(clock(), t)/CLOCKS_PER_SEC);

	/*** V1 ***/
	t = clock();
	V1 = 0;
	for (i = pismall[frthrt-1]+1; i <= pismall[floorsqrt-1]; i++)
	{
		V1 += (i - pi_y) * (i - 2);
	}
	for (i = pismall[floorsqrt-1]; i < pismall[cbrrt-1]; i++)
	{
		p = primes[i];
		V1 += (pismall[x/(p*p)-1] - pismall[p-1]) * (2 - pismall[p-1]);
	}
	printf("V1: %f\n", difftime(clock(), t)/CLOCKS_PER_SEC);

	/*** W2 ***/
	W2 = 0;
	for (i = pismall[max(frthrt, (mint)floor(x/pow(y,2)))-1]; i < pismall[floorsqrt-1]; i++)
	{
		p = primes[i];
		qq = x/(p*(y+1));
		pmin = max(pismall[p-1] + 1, pismall[qq] - pQ[qq] + 1);
		pmax = pismall[min(floor(x/p), floor(sqrt((float)x/(float)p)))-1];
		if (pmin > pmax)
		{
			continue;
		}
		for (j = pmin-1; j < pmax; j++)
		{
			W2 += pismall[x/(p*primes[j])-1];
		}
	}

	/*** W3 ***/
	t = clock();
	W3 = 0;
	w = (pismall[y-1] != pismall[y-2]) ? y : primes[pismall[y-1]-1];
	for (i = pismall[max(frthrt, (mint)floor(x/pow(y,2)))-1]; i < pismall[floorsqrt-1]; i++)
	{
		p = primes[i];
		qq = pismall[floor(sqrt(x/p))-1];
		if (qq > pismall[y-1])
		{
			continue;
		}
		q = primes[qq];
		while (true)
		{
			z = x/(p*q);
			s = (pismall[z-1] != pismall[z-2]) ? z : primes[pismall[z-1]-1];
			qq = min(x/(p*s), y);
			r = min((pismall[qq-1] != pismall[qq-2]) ? qq : primes[pismall[qq-1]-1], w);
			W3 += (pismall[r-1] - pismall[q-1] + 1) * pismall[z-1];
			if (r == w)
			{
				break;
			}
			q = primes[pismall[r-1]];
		}
	}
	printf("W3: %f\n", difftime(clock(), t)/CLOCKS_PER_SEC);

	/*** W4 ***/
	t = clock();
	W4 = 0;
	for (i = pismall[ceilsqrt-1] + (pismall[ceilsqrt-1] == pismall[ceilsqrt-2]) - 1; i < pismall[cbrrt-1]; i++)
	{
		p = primes[i];
		if (pismall[p-1] + 1 <= pismall[floor(sqrt((float)x/(float)p))])
		{
			for (j = pismall[p-1]; j < pismall[floor(sqrt((float)x/(float)p))-1]; j++)
			{
				W4 += pismall[x/(p*primes[j])-1];
			}
		}
	}
	printf("W4: %f\n", difftime(clock(), t)/CLOCKS_PER_SEC);

	/*** W5 ***/
	t = clock();
	W5 = 0;
	for (i = pismall[floorsqrt-1]; i < pismall[cbrrt-1]; i++)
	{
		p = primes[i];
		q = primes[pismall[floor(sqrt((float)x/(float)p))-1]];
		qq = x/(p*p);
		w = (pismall[qq-1] != pismall[qq-2]) ? qq : primes[pismall[qq-1]-1];
		while (true)
		{
			z = x/(p*q);
			s = (pismall[z-1] != pismall[z-2]) ? z : primes[pismall[z-1]-1];
			qq = min(x/(p*s), y);
			r = min((pismall[qq-1] != pismall[qq-2]) ? qq : primes[pismall[qq-1]-1], w);
			W5 += (pismall[r-1] - pismall[q-1] + 1) * pismall[z-1];
			if (r == w)
			{
				break;
			}
			q = primes[pismall[r-1]];
		}
	}
	printf("W5: %f\n", difftime(clock(), t)/CLOCKS_PER_SEC);

	/********************************************
	 ** All PrimePi[z] for y+1 <= z <= Sqrt[x] **
	 ********************************************/

	// In this section we compute:
	//   - all of W1
	//   - part of W2
	
	mint iter = 0;
	t = clock();
	W1 = 0;
	W1Q = (pismall[frthrt-1] + 1 <= pismall[floor(x/pow(y,2))-1]);
	L1 = y+1;
	L2 = 0;
	while (L2 < sqrrt)
	{
		iter++;
		L2 = min(L1+y, sqrrt);
		primeQ = segmentedPrimeQSieve(L1, L2, 1, primes);
		pis = accumulate_plus(primeQ, pi_old);
		pi_old = pis[pis.size()-1];

		if (W1Q)
		{
			for (i = pismall[frthrt-1]; i < pismall[xy2-1]; i++)
			{
				p = primes[i];
				qq = x/(p*(L2+1));
				pmin = max(pismall[p-1] + 1, pismall[qq] - pQ[qq] + 1);
				pmax = pismall[min(x/(L1*p), y) - 1];
				if (pmin > pmax)
				{
					break;
				}
				for (j = pmin-1; j < pmax; j++)
				{
					W1 += pis[x/(p*primes[j]) - L1];
				}
			}
		}

		for (i = pismall[max(frthrt, xy2)-1]; i < pismall[floorsqrt-1]; i++)
		{
			p = primes[i];
			if (p >= sqrt(x/L1))
			{
				break;
			}
			pmin = pismall[max(p, x/(p*(L2+1)))-1] + 1;
			pmax = pismall[min(floor(x/(L1*p)), floor(sqrt((float)x/(float)p)))-1];
			if (pmin > pmax)
			{
				continue;
			}
			for (j = pmin-1; j < pmax; j++)
			{
				W2 += pis[floor(x/(p*primes[j])) - L1];
			}
		}

		L1 = L2 + 1;
	}
	printf("loop 1 iterations: %li\n", iter);
	printf("loop 1: %f\n", difftime(clock(), t)/CLOCKS_PER_SEC);

	/*******************************************
	 ** All PrimePi[z] for Sqrt[x] < z <= x/y **
	 *******************************************/

	// In this section we compute:
	//   - part of W2

	P = (pi_y - pi_old)*(pi_old + pi_y - 1)/2;
	W2Q = (y*y*y*y > x*sqrrt);
	
	iter=0;
	t = clock();
	float totpp = 0;
	while (L2 < CAP)
	{
		iter++;
		L2 = min(L1+y, CAP);
		
		time_t tt = clock();
		primeQ = segmentedPrimeQSieve(L1, L2, 1, primes);
		pis = accumulate_plus(primeQ, pi_old);
		totpp += difftime(clock(), tt)/CLOCKS_PER_SEC;
		
		pi_old = pis[pis.size()-1];
		PP = segmentedPrimeSieve(max(x/(L2+1), y)+1, min(x/L1, sqrrt), 1, primes);

		len = PP.size();
		for (i = 0; i < len; i++)
		{
			p = PP[i];
			P += pis [floor(x/p) - L1];
		}

		if (W2Q)
		{
			for(i = pismall[max(frthrt, xy2)-1]; i < pismall[floorsqrt-1]; i++)
			{
				p = primes[i];
				if (p >= sqrt(x/L1))
				{
					break;
				}
				pmin = pismall[max(p, x/(p*(L2+1)))-1] + 1;
				pmax = pismall[min(floor(x/(L1*p)), floor(sqrt((float)x/(float)p)))-1];
				if (pmin > pmax)
				{
					continue;
				}
				for (j = pmin-1; j < pmax; j++)
				{
					W2 += pis[floor(x/(p*primes[j])) - L1];
				}
			}
		}

		L1 = L2 + 1;
	}
	printf("loop 2 iterations: %li\n", iter);
	printf("loop 2 primeQ accumulate: %f\n", totpp);
	printf("loop 2 total: %f\n", difftime(clock(), t)/CLOCKS_PER_SEC);
	
	t = clock();
	primes.resize(pismall[frthrt-1]);
	S3 = iS3(x, y, primes, mu);
	printf("S3: %f\n", difftime(clock(), t)/CLOCKS_PER_SEC);

	// cout << "S0 = " << S0 << endl;
	// cout << "S1 = " << S1 << endl;
	// cout << "U = "  << U  << endl;
	// cout << "V1 = " << V1 << endl;
	// cout << "W1 = " << W1 << endl;
	// cout << "W2 = " << W2 << endl;
	// cout << "W3 = " << W3 << endl;
	// cout << "W4 = " << W4 << endl;
	// cout << "W5 = " << W5 << endl;
	// cout << "S3 = " << S3 << endl;
	// cout << "pi_y-1 = " << pi_y-1 << endl;
	// cout << "-P = " << -P << endl;

	return S0 + S1 + U + V1 + W1 + W2 + W3 + W4 + W5 + S3 + pi_y-1 - P;
}


/*** Helpers ***/

mint getY(mint x) {
	return (mint)100*floor(floor(pow(x, 0.4))/100);
}

mvector primesInRange(mint n) {

	mint i, k, sqrtn;
	mvector S (n);

	for (i = 2; i <= n; i++)
	{
		S[i-2] = i;
	}

	sqrtn = sqrt(n);
	for (i = 1; i <= sqrtn; i++)
	{
		if (S[i-1] != 0)
		{
			for (k = 2*i+1; k <= n-1; k += i+1)
			{
				S[k-1] = 0;
			}
		}
	}

	/* Remove the 0's */
	S.erase(remove(S.begin(), S.end(), 0), S.end());

	return S;
}

mvector accumulate(mvector lis)
{
	mint len = lis.size();
	mvector acc (len, 0);

	acc[0] = lis[0];
	for (mint i = 1; i < len; i++)
	{
		acc[i] = acc[i-1] + lis[i];
	}

	return acc;
}

mvector accumulate_plus(mvector lis, mint init)
{
	mint len = lis.size();
	mvector acc (len, 0);

	acc[0] = lis[0] + init;
	for (mint i = 1; i < len; i++)
	{
		acc[i] = acc[i-1] + lis[i];
	}

	return acc;
}

mvector range(mint n)
{
	mvector r (n);
	for (mint i = 0; i < n; i++)
	{
		r[i] = i + 1;
	}
	return r;
}

mint mintegerLength(mint n, mint base)
{
	mint number_of_digits = 0;
	do {
		++number_of_digits;
		n /= base;
	} while (n);
	return number_of_digits;
}

mint iS3(mint x, mint y, mvector primes, mvector mu)
{
	mint lg2y, i, j, k, m, p2i, jp2i, p, L1, L2, CAP, S, b, len, elen, qq, phi, r, f, yy;
	mint phi_cache[2] = {0, 0};
	mvector delta, sieve, e;
	mvector phi_old (primes.size()+1, 0);

	S = 0;
	phi = 0;
	f = 0;
	
	time_t tbe;
	float tot = 0;
	
	time_t t = clock();
	delta = segmentedLeastPrimeFactorSieve(1, y, 1, primes);
	printf("S3 --- segmentedLeastPrimeFactorSieve(1, %li): %f\n", y, difftime(clock(), t)/CLOCKS_PER_SEC);
	lg2y = mintegerLength(y, 2) - 1;

	mvector a ((lg2y+1)*(y+1));
	mvector acache ((lg2y+1)*(y+1));
	mint offset = y+1;

	for (i = 0; i <= lg2y; i++)
	{
		p2i  = 1 << i;
		for (j = 1; j <= y+1; j++)
		{
			jp2i = j << i;
			acache[i*offset + j-1] = (jp2i > y) ? max(y-(jp2i-p2i), (mint)0) : p2i;
		}
	}
	
	L1 = 1;
	L2 = 1;
	CAP = ceil((float)x/(float)y);

	time_t loopt = clock();
	while (L2 < CAP)
	{
		L2 = min(L1+y-1, CAP);
		sieve = mvector(L2-L1+1, 1);

		a = acache;

		b = 0;

		len = primes.size();
		for (i = 0; i < len; i++)
		{
			p = primes[i];
			b++;
			phi_cache[0] = 0;
			phi_cache[1] = 0;

			for (m = max(y/p, x/(p*(L2+1)))+1; m <= min(y, x/(p*L1)); m++)
			{
				if (delta[m-1] <= p || mu[m-1] == 0)
				{
					continue;
				}

				qq = x/(m*p);

				if (qq == phi_cache[0])
				{
					S -= mu[m-1]*phi_cache[1];
					continue;
				}

				if (b == 1)
				{
					phi = qq;
				}
				else
				{	
					/* e = binaryExponents(qq-L1+1, lg2y+1);
					phi = phi_old[b-1];

					elen = e.size();
					for (r = 0; r < elen; r++)
					{
						f = (r == 0) ? 0 : (1 << (e[r-1]-e[r])) * (f+1);
						phi += a[e[r]*offset + f];
					} */
					
					phi = phi_old[b-1];
					/*mint l = qq-L1+1;
					mint er = -1;
					mint ll = l;
					mint mask = 0;
					while (ll != 0) {
						er++;
						ll >>= 1;
					}
					ll = l;
					while (er >= 0) {
						phi += a[er*offset + (mask >> er)];
						mask |= 1 << er;
						er--;
						while (er >= 0 && (l & (1 << er)) == 0) {
							er--;
						}
					}*/
					
					mint l = qq-L1+1;
					mint er = 0;
					mint test = 1;
					mint mask = l;
					while (mask > 0) {
						while ((mask & test) == 0) {
							test <<= 1;
							er++;
						}
						mask -= test;
						phi += a[er*offset + (mask >> er)];
					}
				}

				S -= mu[m-1]*phi;
				phi_cache[0] = qq;
				phi_cache[1] = phi;
			}

			if (b == 1)
			{
				phi_old[b-1] = L2;
			}
			else
			{	
				/* e = binaryExponents(L2-L1+1, lg2y+1);
				phi = phi_old[b-1];

				elen = e.size();
				for (r = 0; r < elen; r++)
				{
					f = (r == 0) ? 0 : (1 << (e[r-1]-e[r])) * (f+1);
					phi += a[e[r]*offset + f];
				}
				phi_old[b-1] = phi; */
				
				phi = phi_old[b-1];
				mint l = L2-L1+1;
				mint er = 0;
				mint test = 1;
				mint mask = l;
				while (mask > 0) {
					while ((mask & test) == 0) {
						test <<= 1;
						er++;
					}
					mask -= test;
					phi += a[er*offset + (mask >> er)];
				}
				phi_old[b-1] = phi;
			}

			yy = (L1-1)/p;


			//time_t tt = clock();
			for(k = p*yy + ((p!=2 && yy%2==1)+1)*p; k <= p*(L2/p); k += ((p!=2)+1)*p)
			{
				if (sieve[k-L1] != 0)
				{
					qq = k - L1;
					for (j = 0; j <= lg2y*offset; j += offset)
					{
						a[j + qq]--;
						qq >>= 1;
					}
					sieve[k-L1] = 0;
				}
			}
			//tot += difftime(clock(), tt)/CLOCKS_PER_SEC;
		}

		L1 = L2 + 1;
	}
	//printf("S3 --- update array a: %f\n", tot);
	printf("S3 --- main loop: %f\n", difftime(clock(), loopt)/CLOCKS_PER_SEC);

	return S;
}

mvector binaryExponents(mint n, mint w)
{
	mint i, x, len, temp;
	mvector lis (w, 0);
	mvector res;

	i = 0;
	x = n;
	len = lis.size();

	while (x != 0)
	{
		i--;
		lis[len+i] = x % 2;
		x = x >> 1;
	}

	for (i = 0; i < w; i++)
	{
		temp = (w-i)*lis[i]-1;
		if (temp >= 0)
		{
			res.push_back(temp);
		}
	}

	return res;
}
