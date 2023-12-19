import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two] at h
  rw [Nat.Prime.dvd_mul] at h
  simp at h
  assumption
  exact Nat.prime_two

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    have : 2 ∣ (m ^ 2) := by
      rw [sqr_eq]
      apply Nat.dvd_mul_right
    exact even_of_even_sqr this
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    calc
      2 * (2 * k ^ 2) = (k * 2) ^ 2 := by ring
      _ = m ^ 2 := by rw [meq]
      _ = 2 * n ^ 2 := by rw [sqr_eq]
  have : 2 * k ^ 2 = n ^ 2 := by
    linarith
  have : 2 ∣ n := by
    have : 2 ∣ (n ^ 2) := by
      apply Dvd.intro <;> assumption
    exact even_of_even_sqr this
  have : 2 ∣ m.gcd n := by
    apply Nat.dvd_gcd <;> assumption
  have : 2 ≤ 1 := by
    apply Nat.le_of_dvd
    linarith
    have gcdmn : Nat.gcd m n = 1 := by
      apply coprime_mn
    rwa [← gcdmn]
  linarith

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have : p ∣ m := by
    have : p ∣ (m ^ 2) := by
      rw [sqr_eq]
      apply Nat.dvd_mul_right
    exact prime_p.dvd_of_dvd_pow this
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    calc
      p * (p * k ^ 2) = (k * p) ^ 2 := by ring
      _ = m ^ 2 := by rw [meq]
      _ = p * n ^ 2 := by rw [sqr_eq]
  have : p * k ^ 2 = n ^ 2 := by
    have : p > 0 := by
      apply Nat.Prime.pos
      assumption
    apply Nat.mul_left_cancel this
    linarith
  have : p ∣ n := by
    have : p ∣ (n ^ 2) := by
      apply Dvd.intro <;> assumption
    exact prime_p.dvd_of_dvd_pow this
  have : p ∣ m.gcd n := by
    apply Nat.dvd_gcd <;> assumption
  have : p ≤ 1 := by
    apply Nat.le_of_dvd
    linarith
    have gcdmn : Nat.gcd m n = 1 := by
      apply coprime_mn
    rwa [← gcdmn]
  have : p > 1 := by
    apply Nat.Prime.one_lt
    assumption
  linarith

#check Nat.factors
#check Nat.prime_of_mem_factors
#check Nat.prod_factors
#check Nat.factors_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    sorry
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    sorry
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} (prime_p : p.Prime) :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    sorry
  have eq2 : (r.succ * n ^ k).factorization p =
      k * n.factorization p + r.succ.factorization p := by
    sorry
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  sorry

#check multiplicity
