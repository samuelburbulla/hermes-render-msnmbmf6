/-
OEIS A397588: G.f. A(x) satisfies A(x) = x + (x*A(x)^2)'.
Conjecture (P. D. Hanna, 2026): a(n) is odd iff n is a power of 2, for n ≥ 1.

Proof idea: reading off coefficients, a(n) = [n = 1] + (n+1) [x^n] A(x)^2.
Modulo 2, squaring a power series is the Frobenius map, so A(x)^2 ≡ A(x^2).
Hence a(n) ≡ 0 for odd n > 1 (factor n+1 is even) and a(n) ≡ a(n/2) for even n.
-/
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.FieldTheory.Finite.Basic

open PowerSeries

namespace A397588

/-- Over `ZMod 2`, squaring a power series substitutes `X ↦ X^2`. -/
lemma sq_eq_expand (B : (ZMod 2)⟦X⟧) : B ^ 2 = B.expand 2 two_ne_zero := by
  have h := map_frobenius_expand (R := ZMod 2) (p := 2) two_ne_zero (f := B)
  rw [ZMod.frobenius_zmod, map_id] at h
  exact h.symm

/-- The parity recursion forces `b n = 1` exactly at powers of two. -/
lemma pow2_of_rec (b : ℕ → ZMod 2)
    (hrec : ∀ n, 1 ≤ n →
      b n = (if n = 1 then 1 else 0) + (if 2 ∣ n then b (n / 2) else 0) * ((n : ZMod 2) + 1)) :
    ∀ n, 1 ≤ n → (b n = 1 ↔ ∃ k, n = 2 ^ k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2m with m ≥ 1: b n = b m
    have hm1 : 1 ≤ m := by omega
    have hdvd : 2 ∣ n := ⟨m, by omega⟩
    have hn1 : n ≠ 1 := by omega
    have hdiv : n / 2 = m := by omega
    have hcast : ((n : ZMod 2) + 1) = 1 := by
      rw [hm]; push_cast
      rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
    rw [hrec n hn]
    simp only [hn1, hdvd, ↓reduceIte, hdiv, hcast, zero_add, mul_one]
    rw [ih m (by omega) hm1]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k + 1, by rw [pow_succ]; omega⟩
    · rintro ⟨k, hk⟩
      rcases k with _ | k
      · simp at hk; omega
      · exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · by_cases h1 : n = 1
    · subst h1
      rw [hrec 1 le_rfl]
      constructor
      · intro _; exact ⟨0, rfl⟩
      · intro _; norm_num
    · -- n odd, n > 1: b n = 0
      have hndvd : ¬ 2 ∣ n := by omega
      rw [hrec n hn]
      simp only [h1, hndvd, ↓reduceIte, zero_mul, add_zero]
      constructor
      · intro h; simp at h
      · rintro ⟨k, hk⟩
        rcases k with _ | k
        · simp at hk; omega
        · rw [pow_succ] at hk; omega

/-- **A397588 parity conjecture.** If `A(x) = x + (x * A(x)^2)'` over `ℤ` (for any constant term),
then for `n ≥ 1` the coefficient `a(n)` is odd iff `n` is a power of `2`. -/
theorem odd_coeff_iff (A : ℤ⟦X⟧)
    (hA : A = X + d⁄dX (X * A ^ 2)) (n : ℕ) (hn : 1 ≤ n) :
    Odd (coeff n A) ↔ ∃ k, n = 2 ^ k := by
  set B : (ZMod 2)⟦X⟧ := map (Int.castRingHom (ZMod 2)) A with hB
  -- coefficient recursion over ℤ
  have hcoeff : ∀ m, coeff m A = (if m = 1 then 1 else 0) + coeff m (A ^ 2) * ((m : ℤ) + 1) := by
    intro m
    conv_lhs => rw [hA]
    rw [map_add, coeff_derivative, coeff_succ_X_mul, coeff_X]
  -- reduce mod 2
  have hb : ∀ m, 1 ≤ m → coeff m B =
      (if m = 1 then 1 else 0) + (if 2 ∣ m then coeff (m / 2) B else 0) * ((m : ZMod 2) + 1) := by
    intro m _
    have hsq : coeff m (B ^ 2) = if 2 ∣ m then coeff (m / 2) B else 0 := by
      rw [sq_eq_expand, coeff_expand]
    rw [← hsq, hB, ← map_pow, coeff_map, coeff_map, hcoeff m]
    split_ifs <;> simp
  have key := pow2_of_rec (fun m => coeff m B) hb n hn
  rw [← key, hB, coeff_map]
  simp only [eq_intCast]
  constructor
  · intro hodd
    have : ((coeff n A : ℤ) : ZMod 2) ≠ 0 := by
      rw [Ne, ZMod.intCast_eq_zero_iff_even]; exact Int.not_even_iff_odd.mpr hodd
    exact (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) _ this
  · intro h1
    by_contra hodd
    rw [Int.not_odd_iff_even, ← ZMod.intCast_eq_zero_iff_even] at hodd
    rw [hodd] at h1
    exact absurd h1 (by decide)

/-! ### The OEIS generating function exists (so the theorem is not vacuous) -/

/-- `a(1) = 1`, `a(n) = (n+1) * Sum_{k=1..n-1} a(k) a(n-k)` (recurrence from the OEIS entry). -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => if n = 0 then 1 else ((n : ℤ) + 2) * ∑ k : Fin n, a (k + 1) * a (n - k)
decreasing_by all_goals (have := Fin.is_lt ‹Fin n›; omega)

lemma a_zero : a 0 = 0 := by rw [a]
lemma a_one : a 1 = 1 := by rw [a]; simp
lemma a_add_two (n : ℕ) :
    a (n + 2) = ((n + 1 : ℕ) + 2 : ℤ) * ∑ k : Fin (n + 1), a (k + 1) * a (n + 1 - k) := by
  rw [a]; simp only [show n + 1 ≠ 0 by omega, ↓reduceIte]

lemma coeff_sq_succ (n : ℕ) :
    coeff (n + 1) ((mk a) ^ 2) = ∑ k : Fin n, a (k + 1) * a (n - k) := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ', Finset.sum_range_succ, Fin.sum_univ_eq_sum_range
      (fun k => a (k + 1) * a (n - k))]
  simp only [coeff_mk, a_zero, mul_zero, zero_mul, add_zero, Nat.sub_self]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  omega

/-- The power series with coefficients `a` satisfies `A = x + (x A^2)'` and `A(0) = 0`. -/
theorem mk_a_spec : constantCoeff (mk a) = 0 ∧ mk a = X + d⁄dX (X * (mk a) ^ 2) := by
  refine ⟨by simp [a_zero], ?_⟩
  ext m
  rw [map_add, coeff_derivative, coeff_succ_X_mul, coeff_X, coeff_mk]
  rcases m with _ | n
  · simp [a_zero, pow_two, coeff_mul]
  · rw [coeff_sq_succ]
    rcases n with _ | n
    · simp [a_one]
    · rw [a_add_two]; simp only [show n + 1 + 1 ≠ 1 by omega, ↓reduceIte]
      push_cast; ring

/-- Combining both parts: the OEIS sequence itself has the parity property. -/
theorem a_odd_iff (n : ℕ) (hn : 1 ≤ n) : Odd (a n) ↔ ∃ k, n = 2 ^ k := by
  have := odd_coeff_iff (mk a) mk_a_spec.2 n hn
  simpa [coeff_mk] using this

end A397588
