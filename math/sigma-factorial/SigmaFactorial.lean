/-
When does σ(n) divide n! ?

OEIS A390815 (denominators > 1 of n!/σ(n)) states two conjectures, verified for n ≤ 10^5:
  (1) all terms are prime;
  (2) for n ≥ 4, if σ(n) does not divide n!, then n is a square.
We prove both, via the characterization

  for n ≥ 4 :  σ(n) ∣ n!  ↔  σ(n) is not prime.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open ArithmeticFunction Finset Nat
open scoped ArithmeticFunction.sigma

namespace SigmaFactorial

/-- Two distinct positive integers `≤ n` have product dividing `n!`. -/
lemma mul_dvd_factorial {x y n : ℕ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y)
    (hxn : x ≤ n) (hyn : y ≤ n) : x * y ∣ n ! := by
  rcases lt_or_gt_of_ne hxy with h | h
  · have h1 : x ∣ (y - 1)! := Nat.dvd_factorial hx (by omega)
    have h2 : x * y ∣ y ! := by
      rw [← Nat.mul_factorial_pred (by omega : y ≠ 0), mul_comm x y]
      exact Nat.mul_dvd_mul_left y h1
    exact h2.trans (Nat.factorial_dvd_factorial hyn)
  · have h1 : y ∣ (x - 1)! := Nat.dvd_factorial hy (by omega)
    have h2 : x * y ∣ x ! := by
      rw [← Nat.mul_factorial_pred (by omega : x ≠ 0)]
      exact Nat.mul_dvd_mul_left x h1
    exact h2.trans (Nat.factorial_dvd_factorial hxn)

/-- `σ(p^a) ≤ 2 p^a - 1`. -/
lemma geom_bound_two {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    (∑ k ∈ range (a + 1), p ^ k) + 1 ≤ 2 * p ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ]
    have h : 2 * p ^ a ≤ p ^ (a + 1) := by
      rw [pow_succ]; nlinarith [Nat.one_le_pow a p (by omega)]
    omega

/-- For odd `p`, `σ(p^a) ≤ (3 p^a - 1) / 2`. -/
lemma geom_bound_three {p : ℕ} (hp : 3 ≤ p) (a : ℕ) :
    2 * (∑ k ∈ range (a + 1), p ^ k) + 1 ≤ 3 * p ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ]
    have h : 3 * p ^ a ≤ p ^ (a + 1) := by
      rw [pow_succ]; nlinarith [Nat.one_le_pow a p (by omega)]
    omega

lemma sigma_two : σ 1 2 = 3 := by
  have := sigma_one_apply_prime_pow (p := 2) (i := 1) Nat.prime_two
  simpa [sum_range_succ] using this

/-- Invariant: `σ(m) ∣ k!` for some `k < 2m`, and `2k < 3m` when `m` is odd. -/
lemma exists_small_factorial (m : ℕ) (hm : 0 < m) :
    ∃ k, σ 1 m ∣ k ! ∧ k + 1 ≤ 2 * m ∧ (Odd m → 2 * k + 1 ≤ 3 * m) := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha =>
    refine ⟨σ 1 (p ^ a), Nat.dvd_factorial (by simp [hp.pos]) le_rfl, ?_, ?_⟩
    · rw [sigma_one_apply_prime_pow hp]; exact geom_bound_two hp.two_le a
    · intro hodd
      have hpodd : Odd p := (Nat.odd_pow_iff (by omega)).mp hodd
      have hp3 : 3 ≤ p := by
        have hne : p ≠ 2 := by rintro rfl; exact absurd hpodd (by decide)
        have := hp.two_le; omega
      rw [sigma_one_apply_prime_pow hp]; exact geom_bound_three hp3 a
  | zero => omega
  | one => exact ⟨1, by simp, by norm_num, fun _ => by norm_num⟩
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨ka, hka, hka2, hka3⟩ := iha (by omega)
    obtain ⟨kb, hkb, hkb2, hkb3⟩ := ihb (by omega)
    refine ⟨ka + kb, ?_, ?_, ?_⟩
    · rw [isMultiplicative_sigma.map_mul_of_coprime hab]
      exact (Nat.mul_dvd_mul hka hkb).trans (Nat.factorial_mul_factorial_dvd_factorial_add ka kb)
    · nlinarith
    · intro hodd
      obtain ⟨hao, hbo⟩ := Nat.odd_mul.mp hodd
      have := hka3 hao; have := hkb3 hbo
      nlinarith

/-- If `n = A * B` with `A, B ≥ 2` coprime, then `σ(n) ∣ n!`. -/
lemma sigma_dvd_of_coprime {A B : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) (hAB : Coprime A B) :
    σ 1 (A * B) ∣ (A * B)! := by
  -- the case where one factor is 2
  have two_case : ∀ C : ℕ, 2 ≤ C → Coprime 2 C → σ 1 (2 * C) ∣ (2 * C)! := by
    intro C hC hco
    have hodd : Odd C := Nat.coprime_two_left.mp hco
    obtain ⟨k, hk, -, hk3⟩ := exists_small_factorial C (by omega)
    have hk3 := hk3 hodd
    rw [isMultiplicative_sigma.map_mul_of_coprime hco, sigma_two]
    have h3 : 3 * σ 1 C ∣ 3 ! * k ! := Nat.mul_dvd_mul (by decide) hk
    rcases hodd with ⟨r, rfl⟩
    by_cases hr : r = 1
    · -- C = 3, k ≤ 4
      subst hr
      have hk4 : k ≤ 4 := by omega
      have : 3 ! * k ! ∣ 3 ! * 4 ! := Nat.mul_dvd_mul_left _ (Nat.factorial_dvd_factorial hk4)
      exact h3.trans (this.trans (by decide))
    · -- C ≥ 5, so k + 3 ≤ 2 C
      have hr2 : 2 ≤ r := by omega
      have : k + 3 ≤ 2 * (2 * r + 1) := by omega
      exact h3.trans ((Nat.factorial_mul_factorial_dvd_factorial_add 3 k).trans
        (Nat.factorial_dvd_factorial (by omega)))
  by_cases hA2 : A = 2
  · subst hA2; exact two_case B hB hAB
  by_cases hB2 : B = 2
  · subst hB2; rw [mul_comm]; exact two_case A hA hAB.symm
  -- both factors ≥ 3, not both equal to 3
  have hA3 : 3 ≤ A := by omega
  have hB3 : 3 ≤ B := by omega
  have hne : ¬ (A = 3 ∧ B = 3) := by
    rintro ⟨rfl, rfl⟩; exact absurd hAB (by decide)
  obtain ⟨ka, hka, hka2, -⟩ := exists_small_factorial A (by omega)
  obtain ⟨kb, hkb, hkb2, -⟩ := exists_small_factorial B (by omega)
  rw [isMultiplicative_sigma.map_mul_of_coprime hAB]
  refine (Nat.mul_dvd_mul hka hkb).trans ((Nat.factorial_mul_factorial_dvd_factorial_add ka kb).trans
    (Nat.factorial_dvd_factorial ?_))
  rcases Nat.lt_or_ge A 4 with h | h
  · have hA' : A = 3 := by omega
    have hB4 : 4 ≤ B := by
      by_contra h'; exact hne ⟨hA', by omega⟩
    subst hA'; nlinarith
  · nlinarith

/-- Splitting the geometric sum with an even number of terms. -/
lemma geom_split (p t : ℕ) :
    ∑ k ∈ range (2 * t + 2), p ^ k = (1 + p) * ∑ j ∈ range (t + 1), p ^ (2 * j) := by
  induction t with
  | zero => simp [sum_range_succ]
  | succ t ih =>
    rw [show 2 * (t + 1) + 2 = (2 * t + 2) + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun j => p ^ (2 * j)) (t + 1)]
    ring

lemma half_sum_le {p : ℕ} (hp : 2 ≤ p) (t : ℕ) :
    ∑ j ∈ range (t + 1), p ^ (2 * j) ≤ p ^ (2 * t + 1) := by
  induction t with
  | zero => simp; omega
  | succ t ih =>
    rw [sum_range_succ]
    have e1 : p ^ (2 * (t + 1)) = p ^ (2 * t + 1) * p := by ring
    have e2 : p ^ (2 * (t + 1) + 1) = p ^ (2 * t + 1) * p * p := by ring
    rw [e1, e2]
    have hq : 1 ≤ p ^ (2 * t + 1) := Nat.one_le_pow _ _ (by omega)
    have hpp : 1 + p ≤ p * p := by nlinarith
    have : p ^ (2 * t + 1) * (1 + p) ≤ p ^ (2 * t + 1) * (p * p) := Nat.mul_le_mul_left _ hpp
    nlinarith

/-- Prime powers with odd exponent: `σ(p^a) ∣ (p^a)!` as soon as `p^a ≥ 4`. -/
lemma sigma_prime_pow_odd_dvd {p a : ℕ} (hp : p.Prime) (ha : Odd a) (h4 : 4 ≤ p ^ a) :
    σ 1 (p ^ a) ∣ (p ^ a)! := by
  obtain ⟨t, rfl⟩ := ha
  rw [sigma_one_apply_prime_pow hp]
  have hp2 := hp.two_le
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · -- n = p is an odd prime ≥ 5 and σ(p) = p + 1 = 2 · ((p+1)/2)
    simp [sum_range_succ] at h4 ⊢
    have hodd : Odd p := hp.odd_of_ne_two (by rintro rfl; omega)
    obtain ⟨r, rfl⟩ := hodd
    have hr : 2 ≤ r := by omega
    rw [show 1 + (2 * r + 1) = 2 * (r + 1) by ring]
    exact mul_dvd_factorial (by norm_num) (by omega) (by omega) (by omega) (by omega)
  · -- σ(p^(2t+1)) = (1 + p) · Y with 1 + p < Y ≤ p^(2t+1)
    rw [show 2 * t + 1 + 1 = 2 * t + 2 by ring, geom_split]
    set Y := ∑ j ∈ range (t + 1), p ^ (2 * j) with hY
    have hYle : Y ≤ p ^ (2 * t + 1) := half_sum_le hp2 t
    have hYge : 1 + p ^ 2 ≤ Y := by
      have hsub : range 2 ⊆ range (t + 1) := range_subset_range.mpr (by omega)
      rw [hY]
      calc 1 + p ^ 2 = ∑ j ∈ range 2, p ^ (2 * j) := by simp [sum_range_succ]
        _ ≤ _ := sum_le_sum_of_subset hsub
    have hp3 : 1 + p ≤ p ^ (2 * t + 1) := by
      have : p ^ 3 ≤ p ^ (2 * t + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith [show p ^ 3 = p * p * p by ring]
    exact mul_dvd_factorial (by omega) (by omega) (by nlinarith) hp3 hYle

/-- `n + 1 ≤ σ(n)` for `n ≥ 2`. -/
lemma lt_sigma {n : ℕ} (hn : 2 ≤ n) : n + 1 ≤ σ 1 n := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have h1 : 1 ∈ n.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr (by omega)
  have : 1 ≤ ∑ d ∈ n.properDivisors, d :=
    single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) h1
  omega

/-- Prime powers whose σ is composite: `σ(p^a) ∣ (p^a)!` (for `p^a ≥ 4`). -/
lemma sigma_prime_pow_dvd_of_not_prime {p a : ℕ} (hp : p.Prime) (h4 : 4 ≤ p ^ a)
    (hs : ¬ (σ 1 (p ^ a)).Prime) : σ 1 (p ^ a) ∣ (p ^ a)! := by
  have hp2 := hp.two_le
  have hbound : σ 1 (p ^ a) + 1 ≤ 2 * p ^ a := by
    rw [sigma_one_apply_prime_pow hp]; exact geom_bound_two hp2 a
  have hlow : p ^ a + 1 ≤ σ 1 (p ^ a) := lt_sigma (by omega)
  obtain ⟨u, ⟨v, huv⟩, hu2, hus⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hs
  rw [huv] at hbound hlow ⊢
  have hv2 : 2 ≤ v := by
    rcases Nat.lt_or_ge v 2 with h | h
    · interval_cases v <;> simp_all
    · exact h
  have hun : u ≤ p ^ a := by nlinarith
  have hvn : v ≤ p ^ a := by nlinarith
  by_cases heq : u = v
  · subst heq
    by_cases h8 : 8 ≤ p ^ a
    · -- 4 u² < 8 n ≤ n², so 2u ≤ n
      have h2u : 2 * u ≤ p ^ a := by nlinarith
      have : u * (2 * u) ∣ (p ^ a)! :=
        mul_dvd_factorial (by omega) (by omega) (by omega) hun h2u
      exact (Nat.mul_dvd_mul_left u (Dvd.intro_left 2 rfl)).trans this
    · -- n ∈ {4,…,7} and σ(n) = u² ∈ [n+1, 2n-1] forces u² = 9, i.e. n ∈ {5,6,7};
      -- but σ(5) = 6, σ(7) = 8, and 6 is not a prime power.
      have hu3 : u ≤ 3 := by nlinarith
      have hu' : u = 3 := by
        interval_cases u <;> omega
      subst hu'
      have ha1 : a = 1 := by
        rcases Nat.lt_or_ge a 2 with h | h
        · interval_cases a <;> simp_all
        · have : p ^ 2 ≤ p ^ a := Nat.pow_le_pow_right (by omega) h
          have : p ≤ 2 := by nlinarith
          have hp' : p = 2 := by omega
          subst hp'
          have : 2 ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) (by
            by_contra h'; have : a = 2 := by omega
            subst this; omega)
          omega
      subst ha1
      rw [sigma_one_apply_prime_pow hp] at huv
      simp [sum_range_succ] at huv
      have hp8 : p = 8 := by omega
      subst hp8; exact absurd hp (by decide)
  · exact mul_dvd_factorial (by omega) (by omega) heq hun hvn

/-- A number `n ≥ 2` that is not a prime power splits as a coprime product of two factors `≥ 2`. -/
lemma exists_coprime_split {n : ℕ} (hn : 2 ≤ n) (hpp : ¬ ∃ p a, p.Prime ∧ n = p ^ a) :
    ∃ A B, 2 ≤ A ∧ 2 ≤ B ∧ Coprime A B ∧ n = A * B := by
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hn0 : n ≠ 0 := by omega
  refine ⟨ordProj[p] n, ordCompl[p] n, ?_, ?_, ?_, (Nat.ordProj_mul_ordCompl_eq_self n p).symm⟩
  · have hpos : 0 < n.factorization p :=
      hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n.factorization p := Nat.pow_le_pow_right hp.pos hpos
  · have hpos : 0 < ordCompl[p] n := Nat.ordCompl_pos p hn0
    by_contra h
    have h1 : ordCompl[p] n = 1 := by omega
    apply hpp
    refine ⟨p, n.factorization p, hp, ?_⟩
    have := Nat.ordProj_mul_ordCompl_eq_self n p
    rw [h1, mul_one] at this
    exact this.symm
  · exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)

/-- **Main theorem.** For `n ≥ 4`, `σ(n) ∣ n!` if and only if `σ(n)` is not prime. -/
theorem sigma_dvd_factorial_iff {n : ℕ} (h4 : 4 ≤ n) : σ 1 n ∣ n ! ↔ ¬ (σ 1 n).Prime := by
  constructor
  · intro hdvd hprime
    have := (hprime.dvd_factorial).mp hdvd
    have := lt_sigma (n := n) (by omega)
    omega
  · intro hs
    by_cases hpp : ∃ p a, p.Prime ∧ n = p ^ a
    · obtain ⟨p, a, hp, rfl⟩ := hpp
      exact sigma_prime_pow_dvd_of_not_prime hp h4 hs
    · obtain ⟨A, B, hA, hB, hAB, rfl⟩ := exists_coprime_split (by omega) hpp
      exact sigma_dvd_of_coprime hA hB hAB

/-- **Conjecture 2 of A390815.** For `n ≥ 4`, if `σ(n) ∤ n!` then `n` is a square. -/
theorem isSquare_of_not_dvd {n : ℕ} (h4 : 4 ≤ n) (h : ¬ σ 1 n ∣ n !) : IsSquare n := by
  by_contra hsq
  apply h
  by_cases hpp : ∃ p a, p.Prime ∧ n = p ^ a
  · obtain ⟨p, a, hp, rfl⟩ := hpp
    rcases Nat.even_or_odd a with ⟨b, rfl⟩ | hodd
    · exact absurd ⟨p ^ b, by ring⟩ hsq
    · exact sigma_prime_pow_odd_dvd hp hodd h4
  · obtain ⟨A, B, hA, hB, hAB, rfl⟩ := exists_coprime_split (by omega) hpp
    exact sigma_dvd_of_coprime hA hB hAB

/-- **Conjecture 1 of A390815.** For every `n ≥ 1`, the denominator of `n!/σ(n)` in lowest terms,
`σ(n) / gcd(n!, σ(n))`, is either `1` or a prime. -/
theorem denom_one_or_prime (n : ℕ) (hn : 1 ≤ n) :
    σ 1 n / Nat.gcd (n !) (σ 1 n) = 1 ∨ (σ 1 n / Nat.gcd (n !) (σ 1 n)).Prime := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n
    · left; simp
    · right; rw [show (2 : ℕ) = 2 ^ 1 by rfl, sigma_one_apply_prime_pow Nat.prime_two]; decide
    · right; rw [show (3 : ℕ) = 3 ^ 1 by rfl, sigma_one_apply_prime_pow Nat.prime_three]; decide
  · have hpos : 0 < σ 1 n := by have := lt_sigma (n := n) (by omega); omega
    by_cases hd : σ 1 n ∣ (n)!
    · left
      rw [Nat.gcd_eq_right hd, Nat.div_self hpos]
    · right
      have hprime : (σ 1 n).Prime := by
        by_contra hp; exact hd ((sigma_dvd_factorial_iff h).mpr hp)
      have hcop : Nat.gcd (n !) (σ 1 n) = 1 :=
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hprime).mpr hd))
      rw [hcop, Nat.div_one]
      exact hprime

/-- **A390836 (numerators).** For `n ≥ 4` with `σ(n) ∤ n!`, the reduced numerator
`n! / gcd(n!, σ(n))` is `n!` itself, hence a multiple of `24`. -/
theorem numerator_eq_factorial {n : ℕ} (h4 : 4 ≤ n) (h : ¬ σ 1 n ∣ (n)!) :
    (n)! / Nat.gcd (n)! (σ 1 n) = (n)! ∧ 24 ∣ (n)! / Nat.gcd (n)! (σ 1 n) := by
  have hprime : (σ 1 n).Prime := by
    by_contra hp; exact h ((sigma_dvd_factorial_iff h4).mpr hp)
  have hcop : Nat.gcd (n)! (σ 1 n) = 1 :=
    ((Nat.Prime.coprime_iff_not_dvd hprime).mpr h).symm
  rw [hcop, Nat.div_one]
  refine ⟨rfl, ?_⟩
  have := Nat.factorial_dvd_factorial h4
  simpa [Nat.factorial] using this

/-- The A390836 comment "all terms are even" fails at its second term:
`n = 3` gives `3!/σ(3) = 6/4 = 3/2`, with odd numerator `3`. -/
theorem numerator_three : (3)! / Nat.gcd (3)! (σ 1 3) = 3 := by
  rw [show (3 : ℕ) = 3 ^ 1 by rfl, sigma_one_apply_prime_pow Nat.prime_three]; decide

end SigmaFactorial
