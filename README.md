# Carry Geometry

Minimal Lean formalization of the **positional foundation** of carry geometry.

The library introduces no carry axiom. Its object of departure is the ordinary
finite positional representation of natural numbers in a base `b > 1`. Carry
propagation is then derived from powers, Euclidean quotient and remainder:

$$
\mathbb N
\longrightarrow b^k
\longrightarrow n=(n\bmod b^k)+b^k\lfloor n/b^k\rfloor
\longrightarrow \text{saturation}
\longrightarrow \text{carry}.
$$

In particular, Lean checks

$$
(n+1)\equiv0\pmod{b^k}
\quad\Longleftrightarrow\quad
n\equiv b^k-1\pmod{b^k}.
$$

Thus adding one carries through the lowest `k` positions exactly when that
block was saturated. The primitive computation `(b^k - 1) + 1 = b^k` resets
the lower residue to zero and transfers exactly one unit to the quotient.

## Why normalization is forced

A raw coefficient list may contain arbitrary natural coefficients and still
represent a valid value

$$
\sum_j a_jb^j.
$$

It is not necessarily a finite-alphabet base-`b` numeral. For every raw
coefficient `a`, Lean proves that the only bounded value-preserving split is

$$
a=(a\bmod b)+b\lfloor a/b\rfloor.
$$

At position `j`, this becomes

$$
a b^j=(a\bmod b)b^j+\lfloor a/b\rfloor b^{j+1}.
$$

Thus `a % b` is the restored digit and `a / b` is the forced carry. The
library also proves that the finite digit alphabet is not closed under raw
addition for any `b > 1`, while complete normalization preserves value and
restores every digit to the alphabet.

Exactly `k` finite base-`b` positions contain `b^k` admissible states, and
evaluation bijects those strings with the residual interval `[0, b^k)`.
This is the precise finite-alphabet/exponential-compression mechanism behind
the probability space.

The sexagesimal checks from the motivating calculation are kernel-checked in
[`CarryGeometry.Examples.Sexagesimal`](CarryGeometry/Examples/Sexagesimal.lean).
Lean stores digits least-significant first, so its `[1, 58]` and `[59, 2, 57]`
are the conventional `[58, 1]₆₀` and `[57, 2, 59]₆₀`.

## From arithmetic carry to quadratic rigidity

The saturated pre-increment state is one residual class in `Fin (b ^ k)`.
Every residual class is equiprobable, so the carry-producing class has mass
`b⁻ᵏ`. For every base `b > 1`, positive depth `k`, and real exponent `sigma`,
the library proves

$$
P_b(\{a\})=b^{-k},
\qquad
\bigl(b^{-k/2}\bigr)^2=b^{-k},
$$

and

$$
\bigl(b^{-k\sigma}\bigr)^2=b^{-k}
\quad\Longleftrightarrow\quad
\sigma=\frac12.
$$

Consequently, the globally compatible exponent is unique and independent of
the positional base. No primality assumption is used.

## Exact finite camera transport

The evaluation bijection is exposed as

$$
\operatorname{DigitWindow}(b,k)\simeq\operatorname{Fin}(b^k).
$$

Consequently, two finite camera windows admit an exact coordinate change when
their state counts agree, $b^k=c^\ell$. The resulting equivalence preserves
the represented natural number, its reverse is the opposite camera change,
and changes compose coherently through intermediate cameras.

The API deliberately does not manufacture a bijection when $b^k\ne c^\ell$.
For matched windows it also defines the compression-weighted transform

$$
T_{b,k\to c,\ell}=C_{c,\ell}^{-1}PC_{b,k},
\qquad C_{b,k}x=b^{-k/2}x,
$$

and proves the exact intertwining identity

$$
C_{c,\ell}T_{b,k\to c,\ell}=PC_{b,k}.
$$

This gives kernel-checked preservation of compressed quadratic energy and of
the compressed centered three-point bracket. The definitions and proofs are
in `CarryGeometry.WindowEquiv` and `CarryGeometry.WeightedTransform`.

The public consolidation results are:

- `CarryGeometry.positionalCarryUniversality`, parametrized by an arbitrary
  residual class;
- `CarryGeometry.arithmeticCarryUniversality`, specialized to the class whose
  saturation is proved equivalent to arithmetic carry propagation.

The conditions `b > 1` and `k > 0` are sharp. The API also proves that depth
zero and base one cannot determine the exponent.

## Scope

The positional foundation remains an arithmetic and scalar kernel. The camera
transport modules are an explicitly separated finite extension of that
kernel; they add no Green identity, Weyl machinery, primes, zeta functions,
spectral operators, or analytic continuation. See
[the foundational-core note](docs/FOUNDATIONAL_CORE.md) for the mathematical
contract, and [the forced-normalization note](docs/FORCED_NORMALIZATION.md)
for the structural theorem and its exact scope.

## Build

The project uses Lean `v4.32.0` and the matching pinned Mathlib revision.

```bash
lake exe cache get
lake build --wfail CarryGeometry
lake build --wfail CarryGeometry.Audit
lake build --wfail CarryGeometry.Examples.Sexagesimal
```

## Provenance and license

The foundational laws were distilled from
[`native-carry-geometry`](https://github.com/thiagomassensini/native-carry-geometry)
and retain its Apache-2.0 licensing. The present repository packages the
minimal dependency chain and closes the arbitrary-residue-class formulation.

## Citation and archival

Versioned citation metadata is provided in [`CITATION.cff`](CITATION.cff).
Zenodo-specific release metadata is provided in [`.zenodo.json`](.zenodo.json),
which is authoritative for Zenodo ingestion. Tagged GitHub releases are
archived through the repository's active Zenodo integration.
