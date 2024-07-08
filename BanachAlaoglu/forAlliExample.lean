import Mathlib
/-- The definition of limit for real number sequence -/
def HasLimit (xs : ℕ → ℝ) (x : ℝ) := ∀ ε > 0, ∃ n, ∀ m > n, |xs m - x| < ε

theorem limitAdd (xs ys : ℕ → ℝ) (x y : ℝ) (h1 : HasLimit xs x) (h2 : HasLimit ys y) :
    HasLimit (xs + ys) (x + y) := by
  unfold HasLimit at *
  intro ε hε
  have half_ε_pos : ε / 2 > 0 := by linarith
  specialize h1 (ε / 2) half_ε_pos
  specialize h2 (ε / 2) half_ε_pos
  obtain ⟨n1, hn1⟩ := h1
  obtain ⟨n2, hn2⟩ := h2
  use (max n1 n2)
  intro m hm
  specialize hn1 m (by sorry)
  specialize hn2 m (by sorry)
  calc |(xs + ys) m - (x + y)|
   _ = |(xs m - x) + (ys m - y)|   := by sorry
   _ ≤ |xs m - x| + |ys m - y|   := by exact abs_add (xs m - x) (ys m - y)
   _ < ε/2 + ε/2                 := by apply add_lt_add hn1 hn2
   _ = ε                         := by ring
