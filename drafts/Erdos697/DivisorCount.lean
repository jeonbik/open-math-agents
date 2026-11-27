import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset
namespace Erdos697Work

/-- Positive integers at most N hit by one of a finite family of divisors. -/
theorem count_divisor_union (D : Finset ℕ) (N : ℕ) :
    ((range N).filter (fun i => ∃ d ∈ D, d ∣ i + 1)).card ≤
      ∑ d ∈ D, N / d := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert a D ha ih =>
    let A := (range N).filter (fun i => a ∣ i + 1)
    let B := (range N).filter (fun i => ∃ d ∈ D, d ∣ i + 1)
    have cover : (range N).filter (fun i => ∃ d ∈ insert a D, d ∣ i + 1) = A ∪ B := by
      ext i
      simp [A, B, and_or_left]
    rw [cover, Finset.sum_insert ha]
    exact (Finset.card_union_le A B).trans (Nat.add_le_add (Nat.card_multiples N a).le ih)

#print axioms count_divisor_union
end Erdos697Work
