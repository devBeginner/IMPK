
/*

 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>


void f2m_rand(uint32_t t, uint32_t m, uint32_t *A);
void f2m_print(uint32_t t,uint32_t *A);
uint32_t f2m_is_equal(uint32_t t,uint32_t *A,uint32_t *B);
void copy_array(uint32_t t,uint32_t *A,uint32_t *B);
void add(uint32_t t,uint32_t *A,uint32_t *B);
void shift_left(uint32_t t,uint32_t *A,uint32_t n);
void shift_right(uint32_t t,uint32_t *A,uint32_t n);
void multiply_l2r_kamm(uint32_t t,uint32_t *A,uint32_t *B,uint32_t *C);
uint32_t getDegree(uint32_t t, uint32_t *A);
void invers_stein(uint32_t t, uint32_t *A, uint32_t *B, uint32_t *F);
void mult_scalar(uint32_t m,uint32_t *F,uint32_t *a,uint32_t *b,uint32_t *d,uint32_t *xP,uint32_t *yP,uint32_t *xQ,uint32_t *yQ);


//____________________________________________________________________________________________________________________________________________________________ // Hilfsfunktionen

/*
 * FUNCTION
 *   f2m_rand
 *
 * INPUT
 *   + length t of array A
 *   + bit length m of value represented by A
 *
 * OUTPUT
 *   + random m-bit value in array A
 *
 * RETURN
 *   -
 *
 * DESCRIPTION/REMARKS
 *   The random number generator "rand()" is used. The memory of A must
 *   already be allocated before the function is called.
 */
void f2m_rand(
              uint32_t t,
              uint32_t m,
              uint32_t *A
              )
{
    uint32_t i;
    for (i = 0; i < t-1; i++) A[i] = rand();
    A[t-1] = rand() & (0xFFFFFFFF >> (32 - m % 32));
}



/*
 * FUNCTION
 *   f2m_print
 *
 * INPUT
 *   + length t of array A
 *   + array A
 *
 * OUTPUT
 *   -
 *
 * RETURN
 *   -
 *
 * DESCRIPTION/REMARKS
 *   The function prints the array A in hexadecimal representation
 *   onto the sceen. The least significant bit is aligned to the
 *   right hand side.
 */
void f2m_print(
               uint32_t t,
               uint32_t *A
               )
{
    uint32_t i;
    printf("0x");
    for (i = 0; i < t; i++) printf("%.8X ",A[t-i-1]);
    printf("\n");
}


/*
 * FUNCTION
 *   f2m_is_equal
 *
 * INPUT
 *   + length t of all arrays
 *   + array A
 *   + array B
 *
 * OUTPUT
 *   -
 *
 * RETURN
 *   + 1 (=true) if the content of A and B is equal
 *   + 0 (=false) otherwise
 *
 * DESCRIPTION/REMARKS
 *   -
 */
uint32_t f2m_is_equal(
                      uint32_t t,
                      uint32_t *A,
                      uint32_t *B
                      )
{
    uint32_t i;
    for (i = 0; i < t; i++) if (A[i] != B[i]) return 0;
    return 1;
}

/*
 * FUNCTION
 *   Creates of copy of a polynomial
 *
 * INPUT
 *   + length t of all arrays
 *   + array A
 *   + array B
 */
void copy_array(
                uint32_t t,
                uint32_t *A,
                uint32_t *B
                )
{
uint32_t i;
for (i = 0; i < t; i++) B[i] = A[i]; //erster Wert wird in zweiten Wert kopiert
}

//____________________________________________________________________________________________________________________________________________________________ // Addition

/*
 * FUNCTION
 *   add
 *
 * INPUT
 * 	+ length t of all arrays
 *   + array A
 * 	+ array B
 *
 * OUTPUT
 *   - array A = A+B
 *
 * RETURN
 *   -
 *
 * DESCRIPTION/REMARKS
 *
 */
void add(                       //Alg. 2.32, S. 47 Guide to elliptic Curve
         uint32_t t,
         uint32_t *A,
         uint32_t *B
         )
{
uint32_t i;
for (i = 0; i < t; i++) A[i] ^= B[i];
return;
}



//____________________________________________________________________________________________________________________________________________________________ // Right-/Left - Shift


/*
 * FUNCTION
 *   shift_left
 *
 * INPUT
 * 	+ length t of all arrays
 *   + array A
 *   + number of shifts n
 *
 * OUTPUT
 *   - array A = A << 1
 *
 * RETURN
 *   -
 *
 * DESCRIPTION/REMARKS
 *
 */
void shift_left(
                uint32_t t,
                uint32_t *A,
                uint32_t n
                )
{
int i;
A[t-1] = A[t-1] <<n;
for (i = t-2; i >= 0; i--)
    {
A[i+1] |= (A[i] >>(32-n));
A[i] = A[i] <<n;
}
return;
}


/*
 * FUNCTION
 *   shift_right
 *
 * INPUT
 * 	+ length t of all arrays
 *   + array A
 *   + number of shifts n
 *
 * OUTPUT
 *   - array A = A >> 1
 *
 * RETURN
 *   -
 *
 * DESCRIPTION/REMARKS
 *
 */
void shift_right(
                 uint32_t t,
                 uint32_t *A,
                 uint32_t n
                 )
{
uint32_t i;
A[0] = A[0] >>n;
for (i = 1; i < t; i++)
    {
A[i-1] |= A[i] <<(32-n);
A[i] = A[i] >>n;
}
return;
}




//____________________________________________________________________________________________________________________________________________________________ // Multiplikation + Reduktion


/*
 * FUNCTION
 *   mult_array
 *
 * INPUT
 * 	+ length t of all arrays
 *   + array A
 *   + array B
 *
 * OUTPUT
 *   - array C = A * B
 *
 * RETURN
 *   -
 *
 * DESCRIPTION/REMARKS
 *
 */
void multiply_l2r_kamm(            //Alg. 2.35, S. 50 Guide to elliptic Curve
                         uint32_t t,
                         uint32_t *A,
                         uint32_t *B,
                         uint32_t *C
                         )
{
    uint32_t D[12] = { },
    kth_bit = 0x80000000,
    T,
    *Zeiger_D;
    int k, j;
    for (k = 31; k>=0; k--){
        for (j = 0; j<=5; j++){
            Zeiger_D = &D[j];
            if (A[j] & kth_bit)
                add(t, Zeiger_D, B);
        }
        if (k != 0) shift_left(12, D, 1);
        kth_bit >>= 1;
    }
    //Reduzieren                    //Alg 2.41, S. 55 Guide to elliptic Curve
    //f2m_print(12, C);
    for (k = 10; k >=6; k--){
        T = D[k];
        D[k-6] ^= (T << 29);
        D[k-5] = D[k-5] ^ (T << 4) ^ (T << 3) ^ T ^ (T >> 3);
        D[k-4] = D[k-4] ^ (T >> 28) ^ (T >> 29);
    }
    T = D[5] >> 3;
    D[0] = D[0] ^ (T << 7) ^ (T << 6) ^ (T << 3) ^ T;
    D[1] = D[1] ^ (T >> 25) ^ (T >> 26);
    D[5] &= 0x7;
    copy_array(t, D, C);
    return;
}


//____________________________________________________________________________________________________________________________________________________________ // Grad

/*
 * FUNCTION
 * Bestimme den Grad eines Polynoms *
 * INPUT
 *	t length of the Array
 *	array A
 *
 * OUTPUT
 * Grad des Polynoms A
 */
uint32_t getDegree(uint32_t t, uint32_t *A)
{
	int i, y;
	uint32_t shiftMask;
	for(i = t - 1; i >= 0; i--){        
		shiftMask = 0x80000000;
		for(y = 31; y >= 0; y--){
			if(A[i] & shiftMask) return y + (i*32);
			shiftMask >>= 1;
		}
	}
	return 0;
}

//____________________________________________________________________________________________________________________________________________________________ // Inverse

/*
 * FUNCTION
 *   invers_stein
 *
 * INPUT
 * 	+ length t of all arrays
 *   + array A
 *   + irreducible polynomial F
 *
 *
 * OUTPUT
 *   - array B = A^-1
 *
 * RETURN
 *   -
 *
 * DESCRIPTION/REMARKS
 *
 */
void invers_stein(uint32_t t, uint32_t *A, uint32_t *B, uint32_t *F)                //Alg 2.49, S. 59 Elliptic Curve
{
    uint32_t u[6], v[6], g1[6] = { 1 }, g2[6] = { };
    copy_array(t, A, u);
    copy_array(t, F, v);

    
    // Im Falle, dass das Input-Polynom null ist, return zero
    
    while(getDegree(t, u) != 0 && getDegree(t, u) != 0) {
        while (!(u[0] & 1)){
            shift_right(t, u, 1);            
            if (!(g1[0] & 1)) {
                shift_right(t, g1, 1);
            } else {
                add(t, g1, F);
                shift_right(t, g1, 1);
            }
        }     
        while (!(v[0] & 1)) {
            shift_right(t, v, 1);
            if (!(g2[0] & 1)) {
                shift_right(t, g2, 1);
            } else {
                add(t, g2, F);
                shift_right(t, g2, 1);
            }
        }
        if (getDegree(t, u) > getDegree(t, v))
        {
            add(t, u, v);
            add(t, g1, g2);
        }
        else
        {
            add(t, v, u);
            add(t, g2, g1);
        }
    }
    if (getDegree(t, u) == 0)
    {
        copy_array(t, g1, B);
    }
    else
    {
        copy_array(t, g2, B);
    }
    
}

//____________________________________________________________________________________________________________________________________________________________ // Skalarmultiplikation

void ecc_add(uint32_t *xP, uint32_t *yP, uint32_t *xQ, uint32_t *yQ, uint32_t *a) {
	uint32_t lambda[6], lambda_inv[6], xR[6], yR[6];
	uint32_t F[6] = {0x000000C9, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000008};
	//Berechnung λ = ( y1 + y2 ) / ( x1 + x2 )
	copy_array(6, xP, lambda);
	add(6, lambda, xQ);
	invers_stein(6, lambda, lambda_inv, F);
	copy_array(6, yP, lambda);
	add(6, lambda, yQ);
	multiply_l2r_kamm(6, lambda, lambda_inv, lambda);

	//Berechnung xR = λ^2 + λ + x1 + x2 + a
	multiply_l2r_kamm(6, lambda, lambda, xR);
	add(6, xR, lambda);
	add(6, xR, xP);
	add(6, xR, xQ);
	add(6, xR, a);

	//Berechnung yR = λ *( x1 + xR )+ xR + y1
	copy_array(6, xP, yR);
	add(6, yR, xR);
	multiply_l2r_kamm(6, yR, lambda, yR);
	add(6, yR, xR);
	add(6, yR, yP);

	copy_array(6, xR, xP);
	copy_array(6, yR, yP);
}

void ecc_double(uint32_t *xP, uint32_t *yP, uint32_t *b) {
	uint32_t xP2[6], xP2_inv[6], x2P[6], xP_inv[6];
	uint32_t F[6] = {0x000000C9, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000008};

	//Berechnung xR = x^2 + ( b / x^2 )
	multiply_l2r_kamm(6, xP, xP, xP2);
	invers_stein(6, xP2, xP2_inv, F);	
	multiply_l2r_kamm(6, xP2_inv, b, x2P);
	add(6, x2P, xP2);

	//Berechnung yR = x^2 + (x + ( y / x )) * xR + xR
	invers_stein(6, xP, xP_inv, F);
	multiply_l2r_kamm(6, yP, xP_inv, yP);
	add(6, yP, xP);
	multiply_l2r_kamm(6, yP, x2P, yP);
	add(6, yP, x2P);
	add(6, yP, xP2);

	copy_array(6, x2P, xP);
}

/*
 * FUNCTION
 *   mult_scalar
 *
 * INPUT
 *   + extension degree m of the binary field
 *   + irreducible polynom F to generate the finite field
 *   + elliptic curve parameter a
 *   + elliptic curve parameter b
 *   + scalar d with maximum bitlength m
 *   + x-coordinate xP of point P
 *   + y-coordinate yP of point P
 *
 * OUTPUT
 *   + x-coordinate xQ of point Q
 *   + y-coordinate yQ of point Q
 *
 * RETURN
 *   -
 *
 * DESCRIPTION/REMARKS
 *   The function calculates the point Q = dP
 */
void mult_scalar(
                 uint32_t m,
                 uint32_t *F,
                 uint32_t *a,
                 uint32_t *b,
                 uint32_t *d,
                 uint32_t *xP,
                 uint32_t *yP,
                 uint32_t *xQ,
                 uint32_t *yQ
                 )                                  //Alg. 3.40, S. 103 Guide to elliptic Curve
{
	int i, j;
	uint32_t mask, inf_flag = 1;
	for (i = 6; i > 0; i--) {
		mask = 0x80000000;
                
		for (j = 32; j > 0; j--) {
                    
			if (!inf_flag) ecc_double(xQ, yQ, b);
			if (d[i] & mask) {
				if (inf_flag) {
					copy_array(6, xP, xQ);
					copy_array(6, yP, yQ);
					inf_flag = 0;

				} else {
					ecc_add(xQ, yQ, xP, yP, a);
				}
			}
			mask = mask >> 1;
		}
	}
}


/*
 * FUNCTION
 *   test_ecc_b163
 *
 * INPUT
 *   -
 *
 * OUTPUT
 *   -
 *
 * RETURN
 *   + 0 if test passed
 *   + 1 if test failed
 *
 * DESCRIPTION/REMARKS
 *   The function generates random values a(z)
 *   from the binary field generated by the polynomial
 *   f(z) = z^163 + z^7 + z^6 + z^3 + 1.
 *   We have: 11001001 = 0xC9.
 */
uint32_t test_ecc_b163()
{
    uint32_t

    
    m = 163, /* extension degree of binary field */
    t = 6, /* number of 32-bit words needed to store finite field element */

    
    i, /* iteration variable */

    
    xQ[6], /* public key Q */
    yQ[6],
    d[6], /* private key d */

    
    xC[6], /* challenge C */
    yC[6],
    k[6], /* random scalar for challenge generation */

    
    xR[6], /* response R */
    yR[6],

    
    xV[6], /* verification point C */
    yV[6],


    f[6] = {0x000000C9, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000008}, /* irreducible polynomial */

    
    a[6] = {0x00000001, 0x00000000, 0x00000000,
        0x00000000, 0x00000000, 0x00000000}, /* ec parameter a */

    
    b[6] = {0x4A3205FD, 0x512F7874, 0x1481EB10,
        0xB8C953CA, 0x0A601907, 0x00000002}, /* ec parameter b */

    
    xP[6] = {0xE8343E36, 0xD4994637, 0xA0991168,
        0x86A2D57E, 0xF0EBA162, 0x00000003}, /* x-coord. of base point */

    
    yP[6] = {0x797324F1, 0xB11C5C0C, 0xA2CDD545,
        0x71A0094F, 0xD51FBC6C, 0x00000000}, /* y-coord. of base point */

    
    n[6] = {0xA4234C33, 0x77E70C12, 0x000292FE,
        0x00000000, 0x00000000, 0x00000004}; /* order of base point */


    printf("\n************************************************************\n");
    printf("test: scalar multiplication of EC over GF(2^163)\n");
    printf("\nirreducible polynomial to generate GF(2^163)\n");
    printf("f  = ");f2m_print(t,f); printf("\n");
    printf("\nparameter b to determine elliptic curve E of GF(2^163)\n");
    printf("E: y^2 + xy = x^3 + ax^2 + b\n");
    printf("a  = ");f2m_print(t,a); printf("\n");
    printf("b  = ");f2m_print(t,b); printf("\n");
    printf("\nbase point P\n");
    printf("xP = ");f2m_print(t,xP); printf("\n");
    printf("yP = ");f2m_print(t,yP); printf("\n");
    printf("\norder of base point P\n");
    printf("n  = ");f2m_print(t,n); printf("\n");

    
    for (i = 0; i < 10; i++) {
        printf("************************************************************\n");
        printf("test %d\n",i);
        printf("************************************************************\n");
        printf("generate random private key d and corresponding\n");
        printf("public key Q with Q = d * P\n");
        f2m_rand(t,m,d);
        mult_scalar(m,f,a,b,d,xP,yP,xQ,yQ);
        printf("d  = ");f2m_print(t,d); printf("\n");
        printf("xQ = ");f2m_print(t,xQ); printf("\n");
        printf("yQ = ");f2m_print(t,yQ); printf("\n");


        printf("************************************************************\n");
        printf("generate random scalar d and challenge C\n");
        printf("with C = k * P\n");
        f2m_rand(t,m,k);
        mult_scalar(m,f,a,b,k,xP,yP,xC,yC);
        printf("k  = ");f2m_print(t,k); printf("\n");
        printf("xC = ");f2m_print(t,xC); printf("\n");
        printf("yC = ");f2m_print(t,yC); printf("\n");

        
        printf("************************************************************\n");
        printf("generate response R with R = d * C = d * k * P \n");
        mult_scalar(m,f,a,b,d,xC,yC,xR,yR);
        printf("xR = ");f2m_print(t,xR); printf("\n");
        printf("yR = ");f2m_print(t,yR); printf("\n");

        
        printf("************************************************************\n");
        printf("generate verification point V with V = k * Q = k * d * P\n");
        mult_scalar(m,f,a,b,k,xQ,yQ,xV,yV);
        printf("xV = ");f2m_print(t,xV); printf("\n");
        printf("yV = ");f2m_print(t,yV); printf("\n");
        if (!f2m_is_equal(t,xV,xR) || !f2m_is_equal(t,yV,yR)) return 1;
    }
    printf("************************************************************\n");
    printf("test scalar multiplications...\n");
    for (i = 0; i < 10000; i++) mult_scalar(m,f,a,b,n,xP,yP,xQ,yQ);
    return 0;
}


/* 
 * FUNCTION
 *   main 
 */
int main(void)
{
srand(1);
printf("\ntest_ecc_b163: %d\n",test_ecc_b163());
    return 0;
}