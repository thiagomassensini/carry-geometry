# Forced normalization in finite positional systems

## Statement

Let `b > 0` and let `a` be a raw coefficient attached to position `j`. The
coefficient is algebraically meaningful without any bound:

\[
a b^j.
\]

To make the coefficient an admissible digit, require a decomposition

\[
a=d+bq,\qquad 0\le d<b.
\]

Euclidean division proves that this decomposition exists and is unique:

\[
d=a\bmod b,qquad q=\left\lfloor a/b\right\rfloor.
\]

Multiplying the decomposition by the positional weight gives

\[
a b^j
=(a\bmod b)b^j
+\left\lfloor a/b\right\rfloor b^{j+1}.
\]

The second term is carry. It is not an implementation convention: among all
splits that preserve value and return the current coefficient to
`0, ..., b - 1`, it is the unique possible transfer to the next scale.

The Lean theorem `finiteAlphabetNormalization_forced` packages:

1. existence of the canonical bounded split;
2. `a < b` if and only if carry is zero;
3. `b ≤ a` if and only if carry is positive;
4. uniqueness of both the normalized digit and the carry.

## Raw expansions versus positional numerals

A raw expansion is a finite coefficient list interpreted as

\[
\operatorname{value}_b(a_0,\ldots,a_m)
=\sum_{j=0}^{m}a_jb^j.
\]

The coefficients need not be less than `b`. This remains valid algebra, but
it is not necessarily a numeral over the finite alphabet.

`normalizeCoefficients` evaluates the raw expansion and returns the canonical
base-`b` digit list. Lean proves:

\[
\operatorname{value}_b(\operatorname{normalize}_b A)
=\operatorname{value}_b(A),
\]

and, for `b > 1`, every coefficient in the output is below `b`. An already
canonical list with no leading zero is unchanged.

The current foundational object is natural-number arithmetic, so raw
coefficients are in `ℕ`. Signed coefficients in `ℤ` form a broader redundant
representation useful for subtraction; that extension is not required for
the present forcing theorem.

## Failure of coefficientwise closure

For every `b > 1`, the digits `b - 1` and `1` are individually admissible,
but their raw sum is `b`, which is not. Hence the finite alphabet is not
closed under raw addition.

For `b > 2`, raw multiplication also fails to close: `(b - 1)^2` is outside
the alphabet. Binary is the sharp exception for multiplication of two single
digits, but binary addition still overflows at `1 + 1`.

Thus the structural alternative is exact:

* allow unbounded coefficients and keep the raw weighted sum; or
* retain `b` states per position and normalize overflow through carry.

## Compression theorem

For `b > 1`, `admissibleDigitStrings b hb k` contains exactly

\[
b^k
\]

strings. Positional evaluation is a bijection between those length-`k`
strings and the natural interval `[0,b^k)`. This connects the finite alphabet
directly to the residual space used by the probability layer.

Base one does not supply exponential positional compression: every positional
weight is one and there is only one admissible state per fixed position.

## Sexagesimal checks

Lean stores coefficient lists from least to most significant.

### Addition

\[
59+2=61=1+1\cdot60.
\]

Internal list: `[1, 1]`; conventional notation: `[1,1]₆₀`.

### Multiplication

\[
59^2=3481=1+58\cdot60.
\]

Internal list: `[1, 58]`; conventional notation: `[58,1]₆₀`.

### Power

\[
59^3=205379=59+2\cdot60+57\cdot60^2.
\]

Internal list: `[59, 2, 57]`; conventional notation: `[57,2,59]₆₀`.

All three computations are kernel-checked in
`CarryGeometry.Examples.Sexagesimal`.

## Interpretation

This is not a logical paradox and it is not a new axiom. It is a uniqueness
theorem inside the class of finite positional representations:

> finite alphabet + positional weighting + value-preserving arithmetic
> forces normalization by carry whenever a coefficient overflows.
