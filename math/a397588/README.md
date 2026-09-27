# Proof of the parity conjecture for OEIS A397588, checked in Lean

[A397588](https://oeis.org/A397588) (Paul D. Hanna, 2026-07-03): G.f. A(x) satisfies
A(x) = x + (x·A(x)²)′. Terms 1, 3, 24, 285, 4284, 75978, …

> Conjecture: a(n) is odd iff n is a power of 2 for n ≥ 1.

**This is proved here**, and in slightly stronger form: it holds for *every* integer power series
solving A = x + (x·A²)′, whatever its constant term.

## Proof

Comparing coefficients of xⁿ gives a(n) = [n = 1] + (n+1)·[xⁿ]A(x)².

Reduce mod 2. Over 𝔽₂, squaring is the Frobenius map, so A(x)² ≡ A(x²). Therefore
[xⁿ]A² ≡ a(n/2) when n is even and ≡ 0 when n is odd. So:

- n odd, n > 1: n+1 is even, so a(n) ≡ 0.
- n even: n+1 is odd, so a(n) ≡ a(n/2).
- a(1) = 1.

By strong induction, a(n) is odd exactly when n = 2^k. ∎

## Lean verification

`A397588.lean` (Lean 4.35.0-rc3, Mathlib `b63f6e8a68d220e3b3bc4f3792bb53650d375f24`):

| Lean theorem | Statement |
|---|---|
| `odd_coeff_iff` | for any `A : ℤ⟦X⟧` with `A = X + d⁄dX (X * A ^ 2)` and `n ≥ 1`: `Odd (coeff n A) ↔ ∃ k, n = 2 ^ k` |
| `mk_a_spec` | the series with coefficients given by the OEIS recurrence satisfies the equation (so the theorem is not vacuous) |
| `a_odd_iff` | the same statement for the OEIS sequence itself |

The key step uses Mathlib's `map_frobenius_expand` (squaring = `X ↦ X²` substitution over `ZMod 2`).
The file compiles with no errors, warnings or `sorry`; `#print axioms` reports only `propext`,
`Classical.choice`, `Quot.sound`. `#eval` of the Lean definition reproduces the OEIS terms
0, 1, 3, 24, 285, 4284, 75978, …, and a separate numerical check confirmed the pattern for n ≤ 3000.

To check: in a Mathlib checkout at the commit above, run `lake env lean A397588.lean`.

## Is this new? (what was checked)

- The OEIS entry (snapshot of 2026-09-27, last edited 2026-07-04) states it as a conjecture, with no proof.
  No other OEIS entry references A397588.
- Sela Fried's "Further proofs of conjectures from the OEIS" (arXiv:2607.24832, 2026-07-23) covers
  parity conjectures, but none of the OEIS entries that cite it are A39xxxx sequences. I could not read
  the paper itself (arXiv is blocked from this environment), so this is indirect evidence.
- A web search found work on neighbouring Hanna parity conjectures (A397592, A393856), but nothing on A397588.

So, to the best of these checks, the proof is new. It is an elementary argument, not a hard result.
