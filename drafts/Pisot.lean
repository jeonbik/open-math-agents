import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor

namespace OMA.S_oeis_a010905

def a : ℕ → ℤ
  | 0 => 4
  | 1 => 15
  | n + 2 => ⌊((a (n + 1) : ℚ) ^ 2 / (a n : ℚ) + 1 / 2)⌋

private theorem rounded {x y : ℤ} (hx : 4 ≤ x)
    (h : y^2 - 4*x*y + x^2 = 1) :
    ⌊(y : ℚ)^2 / x + 1/2⌋ = 4*y-x := by
  have hx' : (4 : ℚ) ≤ x := by exact_mod_cast hx
  have hp : (0 : ℚ) < x := by linarith
  have h' : (y : ℚ)^2 - 4*x*y + x^2 = 1 := by exact_mod_cast h
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor
  · apply (sub_le_iff_le_add).mp
    apply (le_div_iff₀ hp).mpr
    nlinarith
  · apply (lt_sub_iff_add_lt).mp
    apply (div_lt_iff₀ hp).mpr
    nlinarith

private theorem invariant (n : ℕ) :
    4 ≤ a n ∧ a n ≤ a (n+1) ∧
    a (n+1)^2 - 4*a n*a (n+1) + a n^2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : a (n+2) = 4*a (n+1)-a n := rounded ih.1 ih.2.2
    change 4 ≤ a (n+1) ∧ a (n+1) ≤ a (n+2) ∧ _
    rw [show n.succ + 1 = n+2 by rfl, h]
    exact ⟨by linarith [ih.1, ih.2.1], by linarith [ih.1, ih.2.1], by nlinarith [ih.2.2]⟩

theorem solution : ∀ n : ℕ, 2 ≤ n → a n = 4 * a (n - 1) - a (n - 2) := by
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  have h : a (k+2) = 4*a (k+1)-a k := rounded (invariant k).1 (invariant k).2.2
  simpa [Nat.add_comm] using h

#print axioms solution
end OMA.S_oeis_a010905
