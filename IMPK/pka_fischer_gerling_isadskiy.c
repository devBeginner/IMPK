/*
 * LECTURE
 *   Implementierung moderner Public-Key-Algorithmen
 *   by Michael Braun, Wintersemester 2015/2016
 *
 * PRACTICAL
 *   Implementation of an Ansi C library for elliptic curves
 *   over binary fields.
 *
 * TEAM
 * Fischer, Daniel, Matr.-Nr
 * Gerling, Marius, 726083
 * Isadskiy, Sergey, Matr.-Nr
 *
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

/* Fuer das erstellen von Zufallszahlen auf Basis der Systemzeit 
 * MUSS WIEDER ENTFERNT WERDEN 
 */
#include <time.h>

#define word uint32_t
#define word_bits 32
#define words 6
#define words2 12
#define Poly_F {0x000000C9, 0x00000000, 0x00000000,0x00000000, 0x00000000, 0x00000008}
#define word_mask {0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0x000007F}
#define word_mask2 {0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0x000007F,0, 0, 0, 0, 0, 0}
static const word degree_m = 163;
clock_t start, finish;

void start_clock() {
    start = clock();
}

void stop_clock(char* Fname) {
    finish = clock();
    printf("\n\n*** The Function %s took %.3f s ***\n\n", Fname, (double) (finish - start) / CLOCKS_PER_SEC);
}

void shiftLeft(word t, word* A, word shifts);
void shiftRight(word t, word* A, word shifts);

word getDeg(word t, word* A);

void add(word t, word* A, word* B);
void addAtoBfromIndexB(word* A, word* B, word IndexB);

void pow2(word* A);
void pow2_163(word t, word* A);

void copy(word* A, word* B);
void copy2(word* A, word* B);

void mask(word* A);
void mask2(word* A);

word bitInArray(word bit, word t, word* A);
word bitInWord(word bit, word Int);

void reduce(word* A, word* F);
void reduce2(word* C, word* F);

void multiply(word t, word* A, word* B, word* F, word* ErgPoly);
void R2L_Kamm(word t, word* A, word* B, word* F, word* C);

void R2L_Shift_And_Add(word t, word* A, word* B, word* F, word* ErgPoly);
void L2R_Shift_And_Add(word t, word* A, word* B, word* F, word* ErgPoly);

void L2R_Kamm_Table(word* A, word* B, word* C2);

word f2m_is_equal(word t, word *A, word *B);
void f2m_print(word t, word *A);
void f2m_rand(word t, word m, word *A);

/* EIGENE FUNKTIONEN */

void shiftLeft(word t, word* A, word shifts) {

    word i;

    /* Element ganz links nach links Shiften*/
    A[t - 1] = A[t - 1] << shifts;

    /* Alle nachfolgenden Elemente durchlaufen und die linken Bits des Elements
     * mit dem vorherigen(bereits geshifteten) Element verunden, dann auch 
     * dieses Element shiften */
    for (i = 2; i < (t + 1); i++) {
        A[t - i + 1] |= A[t - i]>>(word_bits - shifts);
        A[t - i] = A[t - i] << shifts;
    }

}

void shiftRight(word t, word* A, word shifts) {

    word i;

    /* Element ganz rechts um nach rechts shiften*/
    A[0] = A[0] >> shifts;

    /* Alle nachfolgenden Elemente durchlaufen und deren niedrigeste Bits mit
     * dem vorherigen Element verunden, dann auch dieses Element shiften */
    for (i = 1; i < t; i++) {
        A[i - 1] |= A[i] << (word_bits - shifts);
        A[i] = A[i] >> shifts;
    }
}

void test_shift() {

    word shift[words] = {0x80000001, 0x80000001, 0x80000001, 0x80000001, 0x80000001, 0x80000001};

    /* SHIFTEN */
    printf("\nshift:\n");
    f2m_print(words, shift);

    printf("\nShiften von shift um 1 nach rechts:\n");
    shiftRight(6, shift, 1);
    f2m_print(words, shift);

    printf("\nShiften von shift um 1 nach links:\n");
    shiftLeft(words, shift, 1);
    f2m_print(words, shift);

    printf("\nShiften von shift um 1 nach links:\n");
    shiftLeft(words, shift, 1);
    f2m_print(words, shift);

    printf("\nShiften von shift um 1 nach rechts:\n");
    shiftRight(6, shift, 1);
    f2m_print(words, shift);


}

word getDeg(word t, word* A) {

    word i, iTmp = 0, iRet = 0;

    /* Alle Arrayelemente vom groessten an durchlaufen, um dasjenige zu finden,
     * in dem als erstes eine 1 auftaucht, als != 0 ist */
    for (i = 1; i <= t; i++) {

        /* Aktuelles Wort zwischen speichern */
        iTmp = A[t - i];

        /* Wenn das Element != 0 ist, also eine 1 besitzt*/
        if (iTmp != 0) {

            /* Offset fuer den Grad bestimmen (Position des 1. Bit des Elementes -1) */
            iRet = word_bits * (t - i) - 1;

            /* Solange das gefundene Element solange um eins nach rechts shiften 
             * bis das Element 0 ist. Bei jedem durchlauf +1 zum Grad hinzufuegen */
            do {
                iRet++;
                iTmp >>= 1;
            } while (iTmp != 0);

            /* Sobald das gefundene Element durchlaufen wurde, dann den ermittelten 
             * Grad zurueck liefern */
            return iRet;
        }
    }

    /* Sollte kein Element != 0 gefunden werden, ist der Grad 0 */
    return 0;
}

void test_getDeg() {

    word deg0[words2] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    word deg1[words2] = {2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    word degMaxU[words2] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1};
    word degMax[words2] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x80000000};

    printf("\n\nPOLYNOM deg0:\n");
    f2m_print(words2, deg0);
    printf("\nGrad=%d \nPOLYNOM deg1:\n", getDeg(words2, deg0));
    f2m_print(words2, deg1);
    printf("\nGrad=%d \nPOLYNOM degMaxU:\n", getDeg(words2, deg1));
    f2m_print(words2, degMaxU);
    printf("\nGrad=%d \nPOLYNOM degMax:\n", getDeg(words2, degMaxU));
    f2m_print(words2, degMax);
    printf("\nGrad=%d\n", getDeg(words2, degMax));

}

/* Die Funktion addiert(XOR) das Array A auf des Array B. 
 * !!! B WIRD VERAENDERT !!!*/
void add(word t, word* A, word* B) {
    //    word i;

    B[0] ^= A[0];
    B[1] ^= A[1];
    B[2] ^= A[2];
    B[3] ^= A[3];
    B[4] ^= A[4];
    B[5] ^= A[5];

    //    for (i = 0; i < t; i++) {
    //        B[i] ^= A[i];
    //    }
}

/* Die Funktion addiert(XOR) das Array A auf des Array B ab.
 * A[0] wird auf B[0+Offset] addiert 
 * !!! B WIRD VERAENDERT !!!*/
void addAtoBfromIndexB(word* A, word* B, word IndexB) {

    word i;
    for (i = 0; i < words; i++) {
        B[i + IndexB] ^= A[i];
    }
}

/* Quadrierung des Polynoms*/
void pow2(word* A) {

    word c[words2] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};



    L2R_Kamm_Table(A, A, c);

    mask2(c);
    copy(c, A);

}

void test_pow2() {

    word a[words] = {0, 0, 0x40000, 0, 0, 0};
    word erg[words] = {0x192, 0, 0, 0, 0, 0};

    printf("\n\n Double \n");
    printf("\nA:      ");
    f2m_print(words, a);

    printf("\nDouble: ");
    pow2(a);
    f2m_print(words, a);

    printf("\nZiel:   ");
    f2m_print(words, erg);

    printf("\n");

}

/* Array A nach Array B kopieren (Anzahl der Elemente ist durch Konstante 
 * words festgelegt, damit das nicht immer uebergeben werden muss) 
 */
void copy(word* A, word* B) {
    word i;
    for (i = 0; i < words; i++) {
        B[i] = A[i];
    }
}

/* Array A nach Array B kopieren (Anzahl der Elemente ist durch Konstante 
 * words2 festgelegt, damit das nicht immer uebergeben werden muss) 
 * words2 besitzt die doppelte Goesse von words
 */
void copy2(word* A, word* B) {
    word i;
    for (i = 0; i < words2; i++) {
        B[i] = A[i];
    }
}

/* Die Funktion maskiert das Uebergebene Array. Die Maske wird bestimmt durch
 * die Konstanten words2 fuer die Anzahl der Elemente, die die Maske besitzt 
 * und word_mask2, welche die Definition der Maske als Array darstellt. 
 */
void mask(word* A) {

    word mask[words] = word_mask;
    word i;

    for (i = 0; i < words; i++) {
        A[i] &= mask[i];
    }
}

void test_mask() {
    word a[words] = {0x80000001, 0x80000001, 0x80000001, 0x80000001, 0x80000001, 0x800100F1};
    printf("\nMASK");
    printf("\nA:      ");
    f2m_print(words, a);
    printf("\nmasked: ");
    mask(a);
    f2m_print(words, a);
    printf("\n");
}

/* Die Funktion maskiert das Uebergebene Array. Die Maske wird bestimmt durch
 * die Konstanten words2 fuer die Anzahl der Elemente, die die Maske besitzt 
 * und word_mask2, welche die Definition der Maske als Array darstellt. 
 */
void mask2(word* A) {

    word mask[words2] = word_mask2;
    word i;

    for (i = 0; i < words2; i++) {
        A[i] &= mask[i];
    }
}

//void test_mask2() {
//    word a[words2] = {0x80000001, 0x80000001, 0x80000001, 0x80000001, 0x80000001, 0xFFFFFFFF, 0, 0, 0, 0, 0, 0x800100F1};
//    printf("\nMASK");
//    printf("\nA:      ");
//    f2m_print(words2, a);
//    printf("\nmasked: ");
//    mask2(a);
//    f2m_print(words2, a);
//    printf("\n");
//}

/* Gibt das bit an der uebergebenen Stelle innerhalb des uebergebenen Elementes zurueck
 */
word bitInWord(word bit, word Int) {

    if (((0x00000001 << bit) & Int) == 0) {
        return 0;
    }
    return 1;

}

void test_bitInWord() {
    /* Bit an einer Stelle testen */
    printf("\n\nTeste Bit %d von 0x80000001: %d", word_bits - 1, bitInWord(word_bits - 1, 0x80000001));
    printf("\nTeste Bit 1 von 0x80000001: %d", bitInWord(1, 0x80000001));
    printf("\nTeste Bit 0 von 0x80000001: %d", bitInWord(0, 0x80000001));
}

/* Gibt das Bit an der uebergebenen Stelle innerhalb des Arrays zurueck
 * t = Anzahl der Arrayelemente
 */
word bitInArray(word bit, word t, word* A) {

    /* Ermitteln, in welchem Element das Bit enthalten ist */
    word faktor = bit / word_bits;

    /* Ermitteln, an welcher Stelle innerhalb des Wortes das Bit steckt */
    word rest = bit % word_bits;

    /* Wort zum maskieren des Bits erstellen und das Bit maskieren */
    word testVal = ((0x00000001) << rest) & A[faktor];

    /* wenn das Bit 0 war, ist auch der Testwert = 0 */
    if (testVal == 0) {
        /*        printf(" get bit %d, faktor=%d shift=%d testval=%d Eintrag von A=%d returning: %d\n", bit, faktor, rest, testVal, A[faktor], 0);
         */
        return 0;
    }

    /* printf(" get bit %d, faktor=%d shift=%d testval=%d Eintrag von A=%d returning: %d\n", bit, faktor, rest, testVal, A[faktor], 1);
     */
    return 1;

}

void reduceBy_163_7_6_3_1_optimized(word* A) {

    word T = 0;

    ///* Erweiterung ohne Schleife
    word w10 = A[10];
    word w9 = A[9];
    word w8 = A[8];
    word w7 = A[7];
    word w6 = A[6];

    A[10] &= 0;
    A[9] &= 0;
    A[8] &= 0;
    A[7] &= 0;
    A[6] &= 0;

    A[5] ^= (w10 << 4) ^ (w10 << 3) ^ (w10) ^ (w10 >> 3) ^ (w9 >> 28) ^ (w9 >> 29);
    T = A[5] >> 3;
    A[5] &= 0x7;
    A[4] ^= (w10 << 29) ^ (w9 << 4) ^ (w9 << 3) ^ (w9) ^ (w9 >> 3) ^ (w8 >> 28) ^ (w8 >> 29);
    A[3] ^= (w9 << 29) ^ (w8 << 4) ^ (w8 << 3) ^ (w8) ^ (w8 >> 3) ^ (w7 >> 28) ^ (w7 >> 29);
    w6 ^= (w10 >> 28) ^ (w10 >> 29);
    A[2] ^= (w8 << 29) ^ (w7 << 4) ^ (w7 << 3) ^ (w7) ^ (w7 >> 3) ^ (w6 >> 28) ^ (w6 >> 29);
    A[1] ^= (w7 << 29) ^ (w6 << 4) ^ (w6 << 3) ^ (w6) ^ (w6 >> 3)^ (T >> 25) ^ (T >> 26);
    A[0] ^= (w6 << 29)^ (T << 7) ^ (T << 6) ^ (T << 3) ^ T;


}

void L2R_Kamm_Table(word* A, word* B, word* ret) {

    int32_t k, j;
    word C2[words2] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

    for (k = word_bits - 1; k >= 0; k--) {

        for (j = 0; j < words; j++) {

            if (bitInWord(k, A[j]) == 1) {

                //                addAtoBfromIndexB(B, C2, j);
                add(words, B, &C2[j]);

            }

        }

        
        if (k != 0) {
            shiftLeft(words2, C2, 1);
        }

    }

    reduceBy_163_7_6_3_1_optimized(C2);

    ret[0] = C2[0];
    ret[1] = C2[1];
    ret[2] = C2[2];
    ret[3] = C2[3];
    ret[4] = C2[4];
    ret[5] = C2[5];

}

uint8_t isOne(word* A) {
    if ((A[1] | A[2] | A[3] | A[4] | A[5]) == 0 && A[0] == 1) return 1;
    return 0;
}

uint8_t isZero(word* A) {
    if ((A[0] | A[1] | A[2] | A[3] | A[4] | A[5]) == 0) return 1;
    return 0;
}

void invers_Stein(word* b) {

    word F[words] = Poly_F;
    word h1[words] = {0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000};
    word h2[words] = {0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000};
    word v[words] = Poly_F;
    word u[words] = {0, 0, 0, 0, 0, 0};

    //    printf("\nInverting: ");
    //    f2m_print(words, b);
    //    printf("\n");

    if (isZero(b)) {
        return;
    }

    copy(b, u);

    while (isOne(u) != 1 && isOne(v) != 1) {

        while ((v[0]&1) == 0) {
            shiftRight(words, v, 1);

            if ((h1[0]&1) == 0) {
                shiftRight(words, h1, 1);
            } else {
                add(words, F, h1);
                shiftRight(words, h1, 1);
            }
        }
        while ((u[0]&1) == 0) {
            shiftRight(words, u, 1);

            if ((h2[0]&1) == 0) {
                shiftRight(words, h2, 1);
            } else {
                add(words, F, h2);
                shiftRight(words, h2, 1);
            }
        }
        if (getDeg(words, v) >= getDeg(words, u)) {
            add(words, u, v);
            add(words, h2, h1);
        } else {
            add(words, v, u);
            add(words, h1, h2);
        }
    }

    if (isOne(v)) {
        copy(h1, b);
    } else {
        copy(h2, b);
    }

}

void test_invers_Stein() {

    word p1[words] = {0x00000001, 0xFF000000, 0xFF0000FF, 0x00000000, 0x00000000, 0x00000001};
    word p2[words] = {0x00000001, 0xFF000000, 0xFF0000FF, 0x00000000, 0x00000000, 0x00000001};
    word erg[words2] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

    printf("\n\nBerechne das Inverse\nvon:  ");
    f2m_print(words, p1);

    printf("\nErg:  ");
    invers_Stein(p1);
    f2m_print(words, p1);

    printf("\nTest: ");
    L2R_Kamm_Table(p1, p2, erg);
    f2m_print(words, erg);
    printf("\n");
}

void PADD(word* xd, word* Xp, word* Zp, word* Xq, word* Zq) {
    /* P ADD ( x D , X P , Z P , X Q , Z Q ) */

    word Xs[words] = {0, 0, 0, 0, 0, 0};
    word Zs[words] = {0, 0, 0, 0, 0, 0};
    word tmp[words] = {0, 0, 0, 0, 0, 0};
    word tmp2[words] = {0, 0, 0, 0, 0, 0};

    /* Zs berechnen */

    L2R_Kamm_Table(Xq, Zp, Zs);
    L2R_Kamm_Table(Xp, Zq, tmp);
    add(words, tmp, Zs);
    pow2(Zs);

    /* Xs berechnen */

    L2R_Kamm_Table(xd, Zs, Xs);

    L2R_Kamm_Table(Xp, Zq, tmp);
    L2R_Kamm_Table(tmp, Xq, tmp2);
    L2R_Kamm_Table(tmp2, Zp, tmp);

    add(words, tmp, Xs);

    /* S nach P kopieren, P ist die Rueckgabe */
    copy(Xs, Xp);
    copy(Zs, Zp);

}

void PDOUBLE(word* b, word* Xp, word* Zp) {

    word Xs[words] = {0, 0, 0, 0, 0, 0};
    word Zs[words] = {0, 0, 0, 0, 0, 0};

    /* Berechne Z */
    pow2(Xp);
    pow2(Zp);

    L2R_Kamm_Table(Xp, Zp, Zs);

    /* Berechne X */
    pow2(Xp);
    pow2(Zp);

    L2R_Kamm_Table(Zp, b, Xs);
    add(words, Xs, Xp);

    copy(Zs, Zp);

}

void tests() {

    srand(time(NULL));

    /*    printf("\ntest_ecc_b163: %d\n", test_ecc_b163());*/
    //
    //    test_shift();
    //    test_getDeg();
    //
    //    test_bitInArray();
    //    test_bitInWord();
    //    
    //    test_mask();
    //    test_mask2();
    //    
    //    test_R2L_Kamm();
    //    test_ltr_Shift_and_Add();
    //    test_reduce2();

    //    test_reduceBy_163_7_6_3_1();
    //    test_L2R_Kamm_Table();

    //    test_invers_Stein();
    test_pow2();
}

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
        word t,
        word m,
        word *A
        ) {
    word i;

    for (i = 0; i < t - 1; i++) A[i] = rand();
    A[t - 1] = rand() & (0xFFFFFFFF >> (32 - m % 32));
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
        word t,
        word *A
        ) {
    word i;
    printf("0x");

    for (i = 0; i < t; i++) printf("%.8X ", A[t - i - 1]);
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
word f2m_is_equal(
        word t,
        word *A,
        word *B
        ) {
    word i;
    for (i = 0; i < t; i++) if (A[i] != B[i]) return 0;

    return 1;
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
        word m,
        word *F,
        word *a,
        word *b,
        word *d,
        word *xP,
        word *yP,
        word *xQ,
        word *yQ
        ) {
    /* TODO */

    int32_t i;
    word inversion[words];
    word Xkp1[words], xP_xkP[words], xP_xkP1[words], xDbl[words], tmp[words];

    /* Montgomery Leiter */

    word Xq[words] = {1, 0, 0, 0, 0, 0};
    word Zq[words] = {0, 0, 0, 0, 0, 0};
    word Xr[words];
    word Zr[words] = {1, 0, 0, 0, 0, 0};


    copy(xP, Xr);

    copy(Zq, yQ);

    for (i = m - 1; i >= 0; i--) {

        if (bitInArray(i, words, d)) {

            PADD(xP, Xq, Zq, Xr, Zr);
            PDOUBLE(b, Xr, Zr);

        } else {

            PADD(xP, Xr, Zr, Xq, Zq);
            PDOUBLE(b, Xq, Zq);
        }

    }
    //    printf("\nXQ: ");
    //    f2m_print(words, Xq);
    //    printf("\nZQ: ");
    //    f2m_print(words, Zq);
    //    printf("\nXR: ");
    //    f2m_print(words, Xr);
    //    printf("\nZR: ");
    //    f2m_print(words, Zr);
    //    printf("\n");

    /* x und x+1 berechnen */

    copy(Zq, inversion);
    invers_Stein(inversion);
    L2R_Kamm_Table(Xq, inversion, xQ);

    copy(Zr, inversion);
    invers_Stein(inversion);
    L2R_Kamm_Table(Xr, inversion, Xkp1);

    /* y berechnen */

    /* Xkp + Xp */
    add(words, yP, yQ); // yQ = yP

    copy(xP, xDbl); // xDbl = xP
    pow2(xDbl); // xDbl = xP^2
    add(words, xDbl, yQ); // yQ = yP + xP ^2

    copy(xP, xP_xkP);
    add(words, xQ, xP_xkP); // xP + xQ(Xkp))

    copy(xP, xP_xkP1);
    add(words, Xkp1, xP_xkP1); // xP + Xkp+1

    L2R_Kamm_Table(xP_xkP, xP_xkP1, tmp); //xQ * xR
    add(words, tmp, yQ); //++

    L2R_Kamm_Table(xP_xkP, yQ, tmp);

    copy(xP, inversion);
    invers_Stein(inversion);
    L2R_Kamm_Table(tmp, inversion, yQ);

    add(words, yP, yQ);


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
word test_ecc_b163() {
    word

    m = 163, /* extension degree of binary field */
            t = 6, /* number of 32-bit words needed to store finite field element */

            i, /* iteration variable */

            xQ[6] = {0, 0, 0, 0, 0, 0}, /* public key Q */
    yQ[6] = {0, 0, 0, 0, 0, 0},
    d[6] = {0, 0, 0, 0, 0, 0}, /* private key d */

    xC[6] = {0, 0, 0, 0, 0, 0}, /* challenge C */
    yC[6] = {0, 0, 0, 0, 0, 0},
    k[6] = {0, 0, 0, 0, 0, 0}, /* random scalar for challenge generation */

    xR[6] = {0, 0, 0, 0, 0, 0}, /* response R */
    yR[6] = {0, 0, 0, 0, 0, 0},

    xV[6] = {0, 0, 0, 0, 0, 0}, /* verification point C */
    yV[6] = {0, 0, 0, 0, 0, 0},

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
    printf("f  = ");
    f2m_print(t, f);
    printf("\n");
    printf("\nparameter b to determine elliptic curve E of GF(2^163)\n");
    printf("E: y^2 + xy = x^3 + ax^2 + b\n");
    printf("a  = ");
    f2m_print(t, a);
    printf("\n");
    printf("b  = ");
    f2m_print(t, b);
    printf("\n");
    printf("\nbase point P\n");
    printf("xP = ");
    f2m_print(t, xP);
    printf("\n");
    printf("yP = ");
    f2m_print(t, yP);
    printf("\n");
    printf("\norder of base point P\n");
    printf("n  = ");
    f2m_print(t, n);
    printf("\n");

    for (i = 0; i < 10; i++) {
        printf("************************************************************\n");
        printf("test %d\n", i);
        printf("************************************************************\n");
        printf("generate random private key d and corresponding\n");
        printf("public key Q with Q = d * P\n");
        f2m_rand(t, m, d);
        mult_scalar(m, f, a, b, d, xP, yP, xQ, yQ);
        printf("d  = ");
        f2m_print(t, d);
        printf("\n");
        printf("xQ = ");
        f2m_print(t, xQ);
        printf("\n");
        printf("yQ = ");
        f2m_print(t, yQ);
        printf("\n");

        printf("************************************************************\n");
        printf("generate random scalar d and challenge C\n");
        printf("with C = k * P\n");
        f2m_rand(t, m, k);
        mult_scalar(m, f, a, b, k, xP, yP, xC, yC);
        printf("k  = ");
        f2m_print(t, k);
        printf("\n");
        printf("xC = ");
        f2m_print(t, xC);
        printf("\n");
        printf("yC = ");
        f2m_print(t, yC);
        printf("\n");

        printf("************************************************************\n");
        printf("generate response R with R = d * C = d * k * P \n");
        mult_scalar(m, f, a, b, d, xC, yC, xR, yR);
        printf("xR = ");
        f2m_print(t, xR);
        printf("\n");
        printf("yR = ");
        f2m_print(t, yR);
        printf("\n");

        printf("************************************************************\n");
        printf("generate verification point V with V = k * Q = k * d * P\n");
        mult_scalar(m, f, a, b, k, xQ, yQ, xV, yV);
        printf("xV = ");
        f2m_print(t, xV);
        printf("\n");
        printf("yV = ");
        f2m_print(t, yV);
        printf("\n");
        if (!f2m_is_equal(t, xV, xR) || !f2m_is_equal(t, yV, yR)) return 1;
    }
    printf("************************************************************\n");
    printf("test scalar multiplications...\n");
    start_clock();
    for (i = 0; i < 1000; i++) mult_scalar(m, f, a, b, n, xP, yP, xQ, yQ);
    stop_clock("1000 Skalarmultiplikationen");

    return 0;
}

/*
 * FUNCTION
 *   main
 */
int main(void) {

    srand(1);
    printf("\ntest_ecc_b163: %d\n", test_ecc_b163());

    //    tests();

    return 0;
}



