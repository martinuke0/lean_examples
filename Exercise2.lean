import Mathlib

----------------------------------------------------------------------------------------
/-
Let `n` and `k` be nonnegative integers with `k ≤ n`. Then

(i) `choose n 0 = choose n n = 1`

-/

example {n k : ℕ} (h : k ≤ n) : Nat.choose n 0 = 1 ∧ Nat.choose n n = 1 := by
  constructor
  {
    exact Nat.choose_zero_right n
  }
  {
    exact Nat.choose_self n
  }


/-

Let `n` and `k` be nonnegative integers with `k ≤ n`. Then

(ii) `choose n k = choose n (n - k)`.
-/

example {n k : ℕ} (h : k ≤ n) : Nat.choose n k = Nat.choose n (n - k) := by
  apply Eq.symm
  exact Nat.choose_symm h


----------------------------------------------------------------------------------------
