#ifndef LIBRARYDEFS_H
#define LIBRARYDEFS_H

#include "WolframLibrary.h"
#include <vector>
using namespace std;

/*** Wolfram LibraryLink requirements ***/

/* Return the version of Library Link */
DLLEXPORT mint WolframLibrary_getVersion()
{
	return WolframLibraryVersion;
}

/* Initialize Library */
DLLEXPORT int WolframLibrary_initialize(WolframLibraryData libData)
{
	return LIBRARY_NO_ERROR;
}

/* Uninitialize Library */
DLLEXPORT void WolframLibrary_uninitialize(WolframLibraryData libData)
{
	return;
}

void vectorToMTensor(vector<mint> V, MTensor &T, WolframLibraryData &libData)
{
	mint i, dims[1];
	mint* data;

	dims[0] = V.size();
	libData->MTensor_new(MType_Integer, 1, dims, &T);
	data = libData->MTensor_getIntegerData(T);
	for (i = 0; i < V.size(); i++)
	{
		data[i] = V[i];
	}
}

#endif /* LIBRARYDEFS_H */
