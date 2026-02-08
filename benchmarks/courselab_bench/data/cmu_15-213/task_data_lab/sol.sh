#!/bin/bash
# Solution script for CS:APP Data Lab
# This script writes a correct bits.c that passes all btest checks and dlc compliance.

cat > bits.c << 'ENDOFFILE'
/* 
 * CS:APP Data Lab 
 * 
 * bits.c - Source file with your solutions to the Lab.
 *          This is the file you will hand in to your instructor.
 *
 * WARNING: Do not include the <stdio.h> header; it confuses the dlc
 * compiler. You can still use printf for debugging without including
 * <stdio.h>, although you might get a compiler warning. In general,
 * it's not good practice to ignore compiler warnings, but in this
 * case it's OK.  
 */

#if 0
/*
 * Instructions to Students:
 *
 * STEP 1: Read the following instructions carefully.
 */

You will provide your solution to the Data Lab by
editing the collection of functions in this source file.

INTEGER CODING RULES:
 
  Replace the "return" statement in each function with one
  or more lines of C code that implements the function. Your code 
  must conform to the following style:
 
  int Funct(arg1, arg2, ...) {
      /* brief description of how your implementation works */
      int var1 = Expr1;
      ...
      int varM = ExprM;

      varJ = ExprJ;
      ...
      varN = ExprN;
      return ExprR;
  }

  Each "Expr" is an expression using ONLY the following:
  1. Integer constants 0 through 255 (0xFF), inclusive. You are
      not allowed to use big constants such as 0xffffffff.
  2. Function arguments and local variables (no global variables).
  3. Unary integer operations ! ~
  4. Binary integer operations & ^ | + << >>
    
  Some of the problems restrict the set of allowed operators even further.
  Each "Expr" may consist of multiple operators. You are not restricted to
  one operator per line.

  You are expressly forbidden to:
  1. Use any control constructs such as if, do, while, for, switch, etc.
  2. Define or use any macros.
  3. Define any additional functions in this file.
  4. Call any functions.
  5. Use any other operations, such as &&, ||, -, or ?:
  6. Use any form of casting.
  7. Use any data type other than int.  This implies that you
     cannot use arrays, structs, or unions.

 
  You may assume that your machine:
  1. Uses 2s complement, 32-bit representations of integers.
  2. Performs right shifts arithmetically.
  3. Has unpredictable behavior when shifting if the shift amount
     is less than 0 or greater than 31.


EXAMPLES OF ACCEPTABLE CODING STYLE:
  /*
   * pow2plus1 - returns 2^x + 1, where 0 <= x <= 31
   */
  int pow2plus1(int x) {
     /* exploit ability of shifts to compute powers of 2 */
     return (1 << x) + 1;
  }

  /*
   * pow2plus4 - returns 2^x + 4, where 0 <= x <= 31
   */
  int pow2plus4(int x) {
     /* exploit ability of shifts to compute powers of 2 */
     int result = (1 << x);
     result += 4;
     return result;
  }

FLOATING POINT CODING RULES

For the problems that require you to implement floating-point operations,
the coding rules are less strict.  You are allowed to use looping and
conditional control.  You are allowed to use both ints and unsigneds.
You can use arbitrary integer and unsigned constants. You can use any arithmetic,
logical, or comparison operations on int or unsigned data.

You are expressly forbidden to:
  1. Define or use any macros.
  2. Define any additional functions in this file.
  3. Call any functions.
  4. Use any form of casting.
  5. Use any data type other than int or unsigned.  This means that you
     cannot use arrays, structs, or unions.
  6. Use any floating point data types, operations, or constants.


NOTES:
  1. Use the dlc (data lab checker) compiler (described in the handout) to 
     check the legality of your solutions.
  2. Each function has a maximum number of operations (integer, logical,
     or comparison) that you are allowed to use for your implementation
     of the function.  The max operator count is checked by dlc.
     Note that assignment ('=') is not counted; you may use as many of
     these as you want without penalty.
  3. Use the btest test harness to check your functions for correctness.
  4. Use the BDD checker to formally verify your functions
  5. The maximum number of ops for each function is given in the
     header comment for each function. If there are any inconsistencies 
     between the maximum ops in the writeup and in this file, consider
     this file the authoritative source.

/*
 * STEP 2: Modify the following functions according the coding rules.
 * 
 *   IMPORTANT. TO AVOID GRADING SURPRISES:
 *   1. Use the dlc compiler to check that your solutions conform
 *      to the coding rules.
 *   2. Use the BDD checker to formally verify that your solutions produce 
 *      the correct answers.
 */


#endif
//1
/* 
 * bitXor - x^y using only ~ and & 
 *   Example: bitXor(4, 5) = 1
 *   Legal ops: ~ &
 *   Max ops: 14
 *   Rating: 1
 */
int bitXor(int x, int y) {
  /* De Morgan's law: x^y = ~(~x & ~y) & ~(x & y) */
  return ~(~x & ~y) & ~(x & y);
}
/* 
 * tmin - return minimum two's complement integer 
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 4
 *   Rating: 1
 */
int tmin(void) {
  /* Tmin = 0x80000000 = 1 << 31 */
  return 1 << 31;
}
//2
/*
 * isTmax - returns 1 if x is the maximum, two's complement number,
 *     and 0 otherwise 
 *   Legal ops: ! ~ & ^ | +
 *   Max ops: 10
 *   Rating: 1
 */
int isTmax(int x) {
  /*
   * Tmax = 0x7FFFFFFF. If x == Tmax, then x+1 == Tmin == 0x80000000,
   * and x + (x+1) == 0xFFFFFFFF == -1, so ~(x + (x+1)) == 0.
   * We also need to exclude x == -1 (0xFFFFFFFF), where x+1 == 0.
   */
  int xp1 = x + 1;
  return !(~(x + xp1)) & !!xp1;
}
/* 
 * allOddBits - return 1 if all odd-numbered bits in word set to 1
 *   where bits are numbered from 0 (least significant) to 31 (most significant)
 *   Examples allOddBits(0xFFFFFFFD) = 0, allOddBits(0xAAAAAAAA) = 1
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 12
 *   Rating: 2
 */
int allOddBits(int x) {
  /* Build mask 0xAAAAAAAA from byte 0xAA, then check (x & mask) == mask */
  int mask = 0xAA;
  mask = mask | (mask << 8);
  mask = mask | (mask << 16);
  return !((x & mask) ^ mask);
}
/* 
 * negate - return -x 
 *   Example: negate(1) = -1.
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 5
 *   Rating: 2
 */
int negate(int x) {
  /* Two's complement negation: -x = ~x + 1 */
  return ~x + 1;
}
//3
/* 
 * isAsciiDigit - return 1 if 0x30 <= x <= 0x39 (ASCII codes for characters '0' to '9')
 *   Example: isAsciiDigit(0x35) = 1.
 *            isAsciiDigit(0x3a) = 0.
 *            isAsciiDigit(0x05) = 0.
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 15
 *   Rating: 3
 */
int isAsciiDigit(int x) {
  /*
   * Check x - 0x30 >= 0 and 0x39 - x >= 0 using sign bit.
   * x - 0x30 = x + (~0x30 + 1), check sign bit is 0.
   * 0x39 - x = 0x39 + (~x + 1), check sign bit is 0.
   */
  int lower = x + (~0x30 + 1);
  int upper = 0x39 + (~x + 1);
  return !((lower | upper) >> 31);
}
/* 
 * conditional - same as x ? y : z 
 *   Example: conditional(2,4,5) = 4
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 16
 *   Rating: 3
 */
int conditional(int x, int y, int z) {
  /*
   * If x != 0: mask = 0xFFFFFFFF, result = y
   * If x == 0: mask = 0x00000000, result = z
   * mask = ~(!x) + 1 gives 0x00000000 when x!=0 and 0xFFFFFFFF when x==0
   * Actually: !x is 0 when x!=0, so ~0+1 = 0... let me redo.
   * mask = (!x + ~0) gives 0xFFFFFFFF when x!=0, 0x00000000 when x==0
   * Nope, let me think again.
   * !!x = 1 when x!=0, 0 when x==0
   * ~(!!x) + 1 = ~1+1 = 0xFFFFFFFE+1 = 0xFFFFFFFF when x!=0
   *            = ~0+1 = 0xFFFFFFFF+1 = 0 when x==0
   */
  int mask = ~(!!x) + 1;
  return (mask & y) | (~mask & z);
}
/* 
 * isLessOrEqual - if x <= y  then return 1, else return 0 
 *   Example: isLessOrEqual(4,5) = 1.
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 24
 *   Rating: 3
 */
int isLessOrEqual(int x, int y) {
  /*
   * Handle overflow: if signs differ, x negative means x <= y.
   * If signs are the same, compute y - x and check sign bit.
   */
  int signx = (x >> 31) & 1;
  int signy = (y >> 31) & 1;
  int diffSign = signx ^ signy;
  /* If signs differ: x<=y iff x is negative (signx==1) */
  /* If signs same: y-x >= 0 means x<=y */
  int diff = y + (~x + 1);
  int diffNeg = (diff >> 31) & 1;
  return (diffSign & signx) | (!diffSign & !diffNeg);
}
//4
/* 
 * logicalNeg - implement the ! operator, using all of 
 *              the legal operators except !
 *   Examples: logicalNeg(3) = 0, logicalNeg(0) = 1
 *   Legal ops: ~ & ^ | + << >>
 *   Max ops: 12
 *   Rating: 4 
 */
int logicalNeg(int x) {
  /*
   * For any nonzero x, either x or -x (or both) has the sign bit set.
   * (x | (~x + 1)) >> 31 gives -1 for nonzero, 0 for zero.
   * Add 1 to get 0 for nonzero, 1 for zero.
   */
  return ((x | (~x + 1)) >> 31) + 1;
}
/* howManyBits - return the minimum number of bits required to represent x in
 *             two's complement
 *  Examples: howManyBits(12) = 5
 *            howManyBits(298) = 10
 *            howManyBits(-5) = 4
 *            howManyBits(0)  = 1
 *            howManyBits(-1) = 1
 *            howManyBits(0x80000000) = 32
 *  Legal ops: ! ~ & ^ | + << >>
 *  Max ops: 90
 *  Rating: 4
 */
int howManyBits(int x) {
  /*
   * If x is negative, flip all bits so we find the position of the
   * highest 1-bit. Then use binary search to find that position.
   * The answer is position + 1 (for the sign bit).
   */
  int sign = x >> 31;
  int b16, b8, b4, b2, b1, b0;

  /* If negative, flip to positive-like representation */
  x = (sign & ~x) | (~sign & x);

  /* Binary search for the highest set bit */
  b16 = !!(x >> 16) << 4;
  x = x >> b16;
  b8 = !!(x >> 8) << 3;
  x = x >> b8;
  b4 = !!(x >> 4) << 2;
  x = x >> b4;
  b2 = !!(x >> 2) << 1;
  x = x >> b2;
  b1 = !!(x >> 1);
  x = x >> b1;
  b0 = x;

  return b16 + b8 + b4 + b2 + b1 + b0 + 1;
}
//float
/* 
 * floatScale2 - Return bit-level equivalent of expression 2*f for
 *   floating point argument f.
 *   Both the argument and result are passed as unsigned int's, but
 *   they are to be interpreted as the bit-level representation of
 *   single-precision floating point values.
 *   When argument is NaN, return argument
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. also if, while
 *   Max ops: 30
 *   Rating: 4
 */
unsigned floatScale2(unsigned uf) {
  unsigned sign = uf & 0x80000000;
  unsigned exp = (uf >> 23) & 0xFF;
  unsigned frac = uf & 0x7FFFFF;

  /* NaN or Infinity: exp == 255, return as-is */
  if (exp == 0xFF)
    return uf;

  /* Denormalized: exp == 0, shift fraction left (may become normalized) */
  if (exp == 0) {
    frac = frac << 1;
    return sign | frac;
  }

  /* Normalized: increment exponent */
  exp = exp + 1;
  if (exp == 0xFF)
    return sign | (0xFF << 23); /* overflow to infinity */

  return sign | (exp << 23) | frac;
}
/* 
 * floatFloat2Int - Return bit-level equivalent of expression (int) f
 *   for floating point argument f.
 *   Argument is passed as unsigned int, but
 *   it is to be interpreted as the bit-level representation of a
 *   single-precision floating point value.
 *   Anything out of range (including NaN and infinity) should return
 *   0x80000000u.
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. also if, while
 *   Max ops: 30
 *   Rating: 4
 */
int floatFloat2Int(unsigned uf) {
  unsigned sign = uf >> 31;
  int exp = ((uf >> 23) & 0xFF) - 127; /* unbiased exponent */
  unsigned frac = (uf & 0x7FFFFF) | 0x800000; /* 1.fraction with implicit 1 */
  int result;

  /* If exponent is negative, |f| < 1, truncates to 0 */
  if (exp < 0)
    return 0;

  /* If exponent >= 31, out of int range */
  if (exp >= 31)
    return 0x80000000u;

  /* Shift fraction to get integer value
   * frac has 23 bits after the implicit 1 (bit 23)
   * We need to shift to align with the exponent
   */
  if (exp > 23)
    result = frac << (exp - 23);
  else
    result = frac >> (23 - exp);

  if (sign)
    result = -result;

  return result;
}
/* 
 * floatPower2 - Return bit-level equivalent of the expression 2.0^x
 *   (2.0 raised to the power x) for any 32-bit integer x.
 *
 *   The unsigned value that is returned should have the identical bit
 *   representation as the single-precision floating-point number 2.0^x.
 *   If the result is too small to be represented as a denorm, return
 *   0. If too large, return +INF.
 * 
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. Also if, while 
 *   Max ops: 30 
 *   Rating: 4
 */
unsigned floatPower2(int x) {
  /*
   * 2^x in IEEE 754 single precision:
   * - Normalized range: exp = x + 127, where 1 <= exp <= 254, i.e. -126 <= x <= 127
   *   Result: exp << 23
   * - Denormalized range: x < -126, down to x = -149 (smallest denorm = 2^-149)
   *   Result: 1 << (x + 149)
   * - Too small: x < -149, return 0
   * - Too large: x > 127, return +INF = 0x7F800000
   */
  if (x > 127)
    return 0x7F800000;  /* +INF */
  if (x >= -126)
    return (x + 127) << 23;  /* normalized */
  if (x >= -149)
    return 1 << (x + 149);  /* denormalized */
  return 0;  /* too small */
}
ENDOFFILE

echo "Solution written to bits.c"
