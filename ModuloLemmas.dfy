

/* lemma ModuloNonNegative(a: int, b: int) */
/* requires b > 0 */
/* ensures 0 <= a % b < b */
/* { } */

lemma TimesOverId(a: nat, m: nat)
requires m > 0
ensures a * m / m == a
{
    assert m / m == 1;
    assert a * m / m == a * (m / m);
}

/* lemma MulMModMZero(a: nat, m: nat) */
/* requires m > 0 */
/* ensures a * m % m == 0 */
/* { */
/*     calc { */
/*         a * m % m; */
/*         == { /1* Definition of modulus *1/ } */
/*         a * m - m * (a * m / m); */
/*         == */
/*         calc { */
/*             a * m / m; */
/*             == */
/*             a; */
/*         } */
/*         /1* == { /2* As (a * m) is clearly divisible by m without any remainder, (a * m / m) will be 'a' *2/ } *1/ */
/*         a * m - m * a; */
/*         == { /1* Rearrange terms *1/ } */
/*         0; */
/*     } */
/* } */

/* lemma MulMModMZero(a: nat, m: nat) */
/* requires m > 0 */
/* ensures a * m % m == 0 */
/* { */
/*     assert a * m / m == a; // Division by m returns a. */
/*     assert a * m - m * a == 0; // Rearrange terms. */
/* } */

/* /1* lemma ModuloAddDistributive(a: int, b: int, m: int) *1/ */
/* lemma ModuloAddDistributive(a: nat, b: nat, m: nat) */
/*    requires m > 0 */
/*    /1* ensures (a + b) % m == (a % m + b % m) % m *1/ */
/* { */
/*     var c := a % m + b % m; */
/*     var d := m * (a / m + b / m); */
/*     var e := a / m + b / m; */
/*     calc { */
/*         d % m; */
/*         == */
/*         m * e % m; */
/*         == */
/*         0; */
/*     } */
/*     /1* calc { *1/ */
/*     /1*     (a + b) % m; *1/ */
/*     /1*     == { /2* Distribute the sum *2/ } *1/ */
/*     /1*     ((a % m + a / m * m) + (b % m + b / m * m)) % m; *1/ */
/*     /1*     == { /2* Group the terms *2/ } *1/ */
/*     /1*     (a % m + b % m + m * (a / m + b / m)) % m; *1/ */
/*     /1*     /2* == *2/ *1/ */
/*     /1*     /2* (c + d) % m; *2/ *1/ */
/*     /1*     /2* { *2/ *1/ */
/*     /1*     /2*     ModuloAddDistributive(c, d, m); *2/ *1/ */
/*     /1*     /2* } *2/ *1/ */
/*     /1*     /2* (c % m + d % m) % m; *2/ *1/ */
/*     /1*     /2* == { /3* Anything modulo m times an integer is 0 *3/ } *2/ *1/ */
/*     /1*     /2* c % m; *2/ *1/ */
/*     /1* } *1/ */
/* } */



/* lemma ModuloIdempotence(a: int, b: int) */
/* requires b > 0 */
/* ensures (a % b) % b == a % b */
/* { } */



/* lemma ModuloOneIsZero(a: int) */
/* ensures a % 1 == 0 */
/* { } */



/* /1* lemma ModuloMulDistributive(a: int, b: int, m: int) *1/ */
/* /1* requires m > 0 *1/ */
/* /1* ensures (a * b) % m == (a % m * b % m) % m *1/ */
/* /1* { } *1/ */



/* lemma DivisorProperties(a: int, b: int) */
/* requires b > 0 */
/* ensures a == (a / b) * b + a % b */
/* { } */



/* lemma ModuloRange(a: int, b: int) */
/* requires b > 0 */
/* ensures 0 <= a % b < b */
/* { } */



/* lemma ModuloPositive(a: int, b: int) */
/* requires b != 0 */
/* ensures a % b >= 0 */
/* { } */



/* /1* lemma ModuloSymmetry(a: int, b: int) *1/ */
/* /1* requires b > 0 *1/ */
/* /1* ensures (-a) % b == (b - (a % b)) % b *1/ */
/* /1* { } *1/ */



/* lemma ModuloTransitive(a: int, b: int, m: int, n: int) */
/* requires m > 0 */
/* requires a % m == b % m */
/* requires a % m == n % m */
/* ensures b % m == n % m */
/* { } */
