# When does σ(n) divide n! ? — proof of the A390815 conjectures, checked in Lean

OEIS [A390815](https://oeis.org/A390815) (denominators > 1 of n!/σ(n), Feb 2026) states two
conjectures, verified there only for n ≤ 10^5:

1. *All terms are prime.*
2. *For n ≥ 4, if σ(n) does not divide n!, then n is a square.*

and R. J. Mathar asks whether the sequence is A062700 (prime values of σ) from the 3rd term on.
The companion entry [A390836](https://oeis.org/A390836) (numerators) claims
*"All terms are even, the third is 24 and all the next ones are multiples of 24"*.

## Prior art (read this first)

The characterization below is **not new as a statement**. OEIS [A325436](https://oeis.org/A325436)
(Jaroslav Krizek, 2019) already says its terms are "the union of the number 3 and numbers m from
A023194 (σ(m) = prime)", which is the same claim. That comment is asserted without a proof in the
entry. And [A023194](https://oeis.org/A023194) has long carried the classical argument that σ(m)
prime forces m to be an even power of a prime, hence a square. Taken together, those two comments
already imply both A390815 conjectures. The 2026 entry just does not cite them.

What this directory adds: a written proof of the A325436 characterization, a machine-checked Lean
formalization of it and of the A390815/A390836 statements, and the observation that A390836's
"all terms are even" fails at its second term. As far as I could tell (the OEIS database snapshot of
2026-09-27 plus a web search), no proof of the A325436 comment has been published, but I did not do
a full literature search.

## Results

**Theorem.** For n ≥ 4:  σ(n) ∣ n!  ⟺  σ(n) is not prime.

Consequences:

- **Conjecture 2 is true.** If σ(n) is prime then n = p^a with a + 1 prime, and n ≥ 4 forces a even,
  so n is a square. (The Lean proof shows the contrapositive directly: non-squares always divide.)
- **Conjecture 1 is true.** The reduced denominator σ(n)/gcd(n!, σ(n)) is 1 or a prime for every n ≥ 1.
- **Mathar's question: yes.** A390815 = 3, 2, followed by σ(n) for n ≥ 4 with σ(n) prime, i.e.
  A390815(k) = A062700(k−1) for k ≥ 3.
- **A390836: "all terms are even" is false** — the second term is 3 (n = 3: 3!/σ(3) = 6/4 = 3/2).
  The rest holds: for n ≥ 4 the numerator is n! itself, so every term after the second is a multiple of 24.

## Proof

Write σ(p^a) = 1 + p + … + p^a. Two elementary facts do all the work:

- (F1) if x ≠ y are positive and both ≤ n, then xy ∣ n!;
- (F2) x!·y! ∣ (x+y)!.

**Bounds for prime powers.** σ(p^a) ≤ 2p^a − 1, and for odd p, 2σ(p^a) + 1 ≤ 3p^a
(both by induction on a).

**Invariant.** For every m ≥ 1 there is k with σ(m) ∣ k!, k + 1 ≤ 2m, and 2k + 1 ≤ 3m if m is odd.
For a prime power take k = σ(m) and use the bounds; for coprime a, b ≥ 2 take k = k_a + k_b and use
σ(ab) = σ(a)σ(b) ∣ k_a!·k_b! ∣ (k_a+k_b)! together with ab ≥ a + b.

**n not a prime power.** Split n = A·B coprime with A, B ≥ 2.
- If A, B ≥ 3 (not both 3): σ(n) ∣ (k_A + k_B)! and k_A + k_B ≤ 2A + 2B − 2 ≤ AB.
- If A = 2 (so B odd): σ(n) = 3σ(B), σ(B) ∣ k! with 2k + 1 ≤ 3B. For B ≥ 5, k + 3 ≤ 2B = n and
  3·k! ∣ 3!·k! ∣ (k+3)! ∣ n!. For B = 3 check n = 6 directly.

**n = p^a with σ(n) composite.** σ(n) = uv with 2 ≤ u ≤ v and uv ≤ 2n − 1, so u, v < n.
If u ≠ v use (F1). If u = v: for n ≥ 8, 4u² < 8n ≤ n² gives 2u ≤ n and u·2u ∣ n!; for n < 8 there is
no case (σ(4) = 7, σ(5) = 6, σ(7) = 8).

**n = p^a with a odd** (used for Conjecture 2): σ(p) = 2·((p+1)/2) for p ≥ 5, and for a = 2t+1 ≥ 3,
σ(p^a) = (1 + p)·(1 + p² + … + p^{2t}) with 1 + p < 1 + p² ≤ second factor ≤ p^a; apply (F1).

**Converse.** If σ(n) is prime it exceeds n, so it cannot divide n!.

## Lean verification

`SigmaFactorial.lean` (Lean 4.35.0-rc3, Mathlib `b63f6e8a68d220e3b3bc4f3792bb53650d375f24`) proves:

| Lean theorem | Statement |
|---|---|
| `sigma_dvd_factorial_iff` | `4 ≤ n → (σ 1 n ∣ n ! ↔ ¬ (σ 1 n).Prime)` |
| `isSquare_of_not_dvd` | `4 ≤ n → ¬ σ 1 n ∣ n ! → IsSquare n` (Conjecture 2) |
| `denom_one_or_prime` | `1 ≤ n → σ/gcd(n!,σ) = 1 ∨ (σ/gcd(n!,σ)).Prime` (Conjecture 1) |
| `numerator_eq_factorial` | `4 ≤ n → ¬ σ 1 n ∣ n ! → numerator = n! ∧ 24 ∣ numerator` |
| `numerator_three` | `3! / gcd(3!, σ 1 3) = 3` (the odd term in A390836) |

No `sorry`; `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

To check: in a Mathlib checkout at the commit above, run `lake env lean SigmaFactorial.lean`.
A numerical cross-check of the characterization for all 4 ≤ n ≤ 200000 also passed.
