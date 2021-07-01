/*============================================================================

    fourierf.c  -  Don Cross <dcross@intersrv.com>

    http://www.intersrv.com/~dcross/fft.html

    Contains definitions for doing Fourier transforms
    and inverse Fourier transforms.

    This module performs operations on arrays of 'float'.

    Revision history:

1998 September 19 [Don Cross]
    Updated coding standards.
    Improved efficiency of trig calculations.

============================================================================*/

// #include <stdlib.h>
// #include <stdio.h>
// #include <math.h>

#include "fourier.h"
#include "ddcmath.h"

#define NULL 0

double
sin(double)
{
	return 0;
}

double
cos(double)
{
	return 0;
}

#define CHECKPOINTER(p)

#define BITS_PER_WORD   (sizeof(unsigned) * 8)


int
IsPowerOfTwo(unsigned x)
{
	if (x < 2)
		return 0;

	if (x & (x - 1))
		return 0;

	return 1;
}


unsigned
NumberOfBitsNeeded(unsigned PowerOfTwo)
{
	unsigned i;

	if (PowerOfTwo < 2) {
		// fprintf(stderr, ">>> Error in fftmisc.c: argument %d to NumberOfBitsNeeded is too small.\n", PowerOfTwo);
		// exit(1);
	}

	i = 0;
	while (1) {
		if (PowerOfTwo & (1 << i))
			return i;
		i++;
	}
}

unsigned
ReverseBits(unsigned index, unsigned NumBits)
{
	unsigned i, rev;

	i = 0;
	rev = 0;
	while (i < NumBits) {
		rev = (rev << 1) | (index & 1);
		index = index >> 1;
		i++;
	}

	return rev;
}

void
fft_float(unsigned NumSamples, int InverseTransform, float *RealIn, float *ImagIn, float *RealOut, float *ImagOut)
{
	unsigned NumBits;	/* Number of bits needed to store indices */
	unsigned i, j, k, n;
	unsigned BlockSize, BlockEnd;
	double angle_numerator = 2.0 * DDC_PI;
	double tr, ti;		/* temp real, temp imaginary */

	i = IsPowerOfTwo(NumSamples);
	if (!i) {
		/* fprintf(stderr, "Error in fft():  NumSamples=%u is not power of two\n", NumSamples); */
		return;
	}
	if (InverseTransform)
		angle_numerator = -angle_numerator;

	CHECKPOINTER(RealIn);
	CHECKPOINTER(RealOut);
	CHECKPOINTER(ImagOut);

	NumBits = NumberOfBitsNeeded(NumSamples);

	/*
	 **   Do simultaneous data copy and bit-reversal ordering into outputs...
	 */
	i = 0;
	while (i < NumSamples) {
		j = ReverseBits(i, NumBits);
		RealOut[j] = RealIn[i];
		if (ImagIn == NULL)
			ImagOut[j] = 0.0;
		else
			ImagOut[j] = ImagIn[i];
		i++;
	}

	/*
	 **   Do the FFT itself...
	 */
	BlockEnd = 1;
	BlockSize = 2;
	while (BlockSize <= NumSamples) {
		double delta_angle = angle_numerator / (double)BlockSize;
		double sm2 = sin(-2 * delta_angle);
		double sm1 = sin(-delta_angle);
		double cm2 = cos(-2 * delta_angle);
		double cm1 = cos(-delta_angle);
		double w = 2 * cm1;
		double ar0, ar1, ar2, ai0, ai1, ai2;
		double temp;

		i = 0;
		while (i < NumSamples) {
			ar2 = cm2;
			ar1 = cm1;
			ai2 = sm2;
			ai1 = sm1;

			j = i;
			n = 0;
			while (n < BlockEnd) {
				ar0 = w * ar1 - ar2;
				ar2 = ar1;
				ar1 = ar0;
				ai0 = w * ai1 - ai2;
				ai2 = ai1;
				ai1 = ai0;
				k = j + BlockEnd;
				tr = ar0 * RealOut[k] - ai0 * ImagOut[k];
				ti = ar0 * ImagOut[k] + ai0 * RealOut[k];
				RealOut[k] = RealOut[j] - tr;
				ImagOut[k] = ImagOut[j] - ti;
				RealOut[j] = RealOut[j] + tr;
				ImagOut[j] = ImagOut[j] + ti;

				j++;
				n++;
			}

			i = i + BlockSize;
		}
		BlockEnd = BlockSize;
		BlockSize = BlockSize << 1;
	}

	/*
	 **   Need to normalize if inverse transform...
	 */
	if (InverseTransform) {
		double denom = (double)NumSamples;

		i = 0;
		while (i < NumSamples) {
			RealOut[i] = RealOut[i] / denom;
			ImagOut[i] = ImagOut[i] / denom;
			i++;
		}
	}
}


/*--- end of file fourierf.c ---*/
