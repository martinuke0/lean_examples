import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic

open Finset BigOperators

----------------------------------------------------------------------------------------
/-

If $a$ and $r$ are real numbers and $r \neq 1$, then
(1.1)
$$
\sum_{j=0}^{n} a r^{j}=a+a r+a r^{2}+\cdots+a r^{n}=\frac{a r^{n+1}-a}{r-1} .
$$
-/

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) : ∑ i ∈ range (n+1), a * r^i = (a * r^(n+1) - a) / (r-1) := by
  induction n with
  | zero => {
    simp
    rw [eq_div_iff_mul_eq]
    ring
    exact sub_ne_zero_of_ne h
  }
  | succ n ih => {
    rw [Finset.sum_range_succ, ih]
    rw [pow_succ (r) (n+1)]

    have h2 : a * r ^ (n + 1) = (a * r ^ (n + 1) * (r - 1)) / (r - 1) := by
      rw [MulDivCancelClass.mul_div_cancel (a * r ^ (n + 1)) (r - 1)]
      exact sub_ne_zero_of_ne h

    nth_rewrite 2 [h2]
    rw [← add_div]
    rw [mul_sub]
    refine (div_left_inj' ?_).mpr ?_
    exact sub_ne_zero_of_ne h
    ring
  }
----------------------------------------------------------------------------------------
