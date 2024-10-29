import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-
We define a function recursively for all positive integers $n$ by $f(1)=1$, $f(2)=5$, 
and for $n>2, f(n+1)=f(n)+2 f(n-1)$. Show that $f(n)=$ $2^{n}+(-1)^{n}$, 
using the second principle of mathematical induction.
-/

----------------------------------------------------------------------------------------
def f :  ℕ → ℤ
| 0     => 2
| 1     => 1
| 2     => 5
| (n+1) => f n + 2 * f (n - 1)

def g (n : ℕ) : ℤ := 2 ^ n + (-1) ^ n

theorem f_eq_g : ∀ n : ℕ, n ≥ 1 → f n = g n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => exfalso; linarith
    | 1 => simp [f, g]
    | 2 => simp [f, g]
    | _ =>
      simp [f, g]
      have h1 := ih (k - 1) (by linarith)
      have h2 := ih (k - 2) (by linarith)
      simp only [f, g] at *
      ring
----------------------------------------------------------------------------------------
