import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Order
import MIL.Common

open BigOperators

namespace C05S03

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat' apply Nat.succ_le_succ
    apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  . rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
    simp [Nat.factorial_succ]
    calc
      2 ≤ (n + 1) * 1 + 1 := by linarith
      _ ≤ (n + 1) * Nat.factorial n + 1 := by
        have : 1 ≤ Nat.factorial n := by
          apply Nat.factorial_pos
        simp [this]
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine' ⟨p, _, pp⟩
  show p > n
  by_contra ple
  push_neg  at ple
  have : p ≥ 2 := Nat.Prime.two_le pp
  have : p ∣ Nat.factorial (n + 1) := by
    apply Nat.dvd_factorial
    exact Nat.Prime.pos pp
    linarith
  show False
  have : p ∣ 1 := by
    exact (Nat.dvd_add_right this).mp pdvd
  have : p ≤ 1 := by
    exact Nat.le_of_dvd zero_lt_one this
open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  simp [ext_iff]
  tauto
example : (r \ s) \ t = r \ (s ∪ t) := by
  simp [ext_iff]
  tauto

end

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i in s, i :=
  Finset.dvd_prod_of_mem _ h

theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  apply (Nat.Prime.eq_one_or_self_of_dvd prime_q) at h
  cases h
  · have : p ≥ 2 := Nat.Prime.two_le prime_p
    linarith
  · assumption

-- If S is a set of primes,
-- then any prime factor of the product of the elements of S is in S.
theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
  intro h₀ h₁
  -- induct on the size of S
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
  rcases h₁ with pdiva | pdvds
  . have aprime : a.Prime := by
      exact h₀.1
    have : p = a := by
      apply Nat.Prime.eq_of_dvd_of_prime prime_p aprime
      assumption
    exact Or.inl this
  . have : p ∈ s := by
      apply ih
      intro n nins
      exact h₀.2 n nins
      exact pdvds
    exact Or.inr this
example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg  at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i in s', i) + 1 := by
    calc
      2 ≤ 1 + 1 := by norm_num
      _ ≤ (∏ i in s', i) + 1 := by
        have : 0 < ∏ i in s', i := by
          apply Finset.prod_pos
          intro i
          rw [mem_s']
          exact Nat.Prime.pos
        linarith
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i in s', i := by
    have : p ∈ s' := by
      rw [mem_s']
      exact pp
    exact Finset.dvd_prod_of_mem _ this
  have pdiv1 : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  have : p ≥ 2 := Nat.Prime.two_le pp
  have : p ≤ 1 := by
    exact (Nat.Prime.dvd_factorial pp).mp pdiv1
  linarith
theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]
  norm_num

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} : (m * n % 4 = 3) → m % 4 = 3 ∨ n % 4 = 3 := by
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases hm : m % 4 <;> simp [hm]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases hn : n % 4 <;> simp [hn] ; decide

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h
#check Nat.div_dvd_of_dvd
#check Nat.div_lt_self

-- If m is a nontrivial divisor of n, then n / m is too.
theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  constructor
  . exact Nat.div_dvd_of_dvd h₀
  . apply Nat.div_lt_self <;> linarith

-- If n % 4 = 3, then n has a prime factor with the same property.
theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) : ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  -- Strong induction on n that are composite, and satisfy n % 4 = 3.
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg  at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
  . have h' : ¬Nat.Prime m → ∃ p, Nat.Prime p ∧ p ∣ m ∧ p % 4 = 3 := ih m mltn h1
    by_cases mp : m.Prime
    . use m
    . apply h' at mp
      rcases mp with ⟨p, pp, pdvdm, p4⟩
      use p
      have pdivn : p ∣ n := by
        exact Nat.dvd_trans pdvdm mdvdn
      exact ⟨pp, pdivn, p4⟩
  have nmdivn : n / m ∣ n := by
    exact Nat.div_dvd_of_dvd mdvdn
  by_cases nmp : (n / m).Prime
  · use n / m
  . have : n / m < n := by
      have : n ≥ 2 := by
        apply two_le_of_mod_4_eq_3 h
      have : n < n * m := by
        calc
          n < n + n := by linarith
          _ = 2 * n := by ring
          _ ≤ m * n := by
            exact Nat.mul_le_mul_right n mge2
          _ = n * m := by ring
      have mpos : m > 0 := by
        linarith
      exact (Nat.div_lt_iff_lt_mul mpos).mpr this
    have h' : ¬Nat.Prime (n/m) → ∃ p, Nat.Prime p ∧ p ∣ (n/m) ∧ p % 4 = 3 := ih (n/m) this h1
    apply h' at nmp
    rcases nmp with ⟨p, pp, pdvdm, p4⟩
    use p
    have pdivn : p ∣ n := by
      exact Nat.dvd_trans pdvdm nmdivn
    exact ⟨pp, pdivn, p4⟩

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption

theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg  at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i in erase s 3, i) + 3) % 4 = 3 := by
    rw [Nat.add_mod, Nat.mul_mod_right]
    norm_num
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
    rw [← hs]
    exact ⟨pp, p4eq⟩
  have pne3 : p ≠ 3 := by
    intro peq3
    rw [peq3] at pdvd
    simp [Nat.add_mod, Nat.mul_mod_right] at pdvd
    have : 3 ∣ 4 * ∏ i in erase s 3, i ↔ 3 ∣ 4  ∨ 3 ∣ ∏ i in erase s 3, i := by
      apply Nat.Prime.dvd_mul
      exact Nat.prime_three
    rw [this] at pdvd
    rcases pdvd with h1 | h2
    · have : ¬ 3 ∣ 4 := by norm_num
      contradiction
    . have threeinserase3 : 3 ∈ s.erase 3 := by
        apply mem_of_dvd_prod_primes
        exact Nat.prime_three
        simp
        intro n neq3 nins
        rw [← hs n] at nins
        exact nins.1
        assumption
      simp at threeinserase3
  have : p ∣ 4 * ∏ i in erase s 3, i := by
    apply Dvd.dvd.mul_left
    apply dvd_prod_of_mem
    rw [Finset.mem_erase]
    exact ⟨pne3, ps⟩
  have : p ∣ 3 := by
    convert (Nat.dvd_sub' pdvd this)
    simp
  have : p = 3 := by
    apply Nat.Prime.eq_of_dvd_of_prime
    exact pp
    exact Nat.prime_three
    exact this
  contradiction
