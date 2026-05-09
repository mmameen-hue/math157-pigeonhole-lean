import Mathlib

example (n : ℕ) (h : 0 < n) :
  ¬ ∃ f : Fin (n + 1) → Fin n, Function.Injective f := by
  sorry
