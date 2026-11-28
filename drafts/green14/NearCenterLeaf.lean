import MiddleEncoding
import SplitCertificate

open Std.Sat
namespace Green14MiddleEncoding
theorem no_adjacent_red_pair : (withLiteral (withLiteral h11 78 true) 80 true).Unsat := by
  intro a
  cases h : a 78 <;> cases k : a 80 <;> simp [withLiteral, CNF.eval, CNF.Clause.eval, h, k]
  have mem : [(78, false), (80, false)] ∈ h11.clauses := by
    simp [h11, formula, centeredRows, List.mem_map]
    exact Or.inr (Or.inr ⟨0, by decide, rfl, rfl⟩)
  obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp mem
  refine ⟨i, hi, ?_⟩
  simp [he, not_and]
  grind
#print axioms no_adjacent_red_pair

/-- The two branches still required for the first near-center formula. -/
theorem h11_of_remaining
    (leftBlue : (withLiteral h11 78 false).Unsat)
    (leftRedRightBlue : (withLiteral (withLiteral h11 78 true) 80 false).Unsat) :
    h11.Unsat := by
  exact split_unsat _ 78 leftBlue
    (split_unsat _ 80 leftRedRightBlue no_adjacent_red_pair)
#print axioms h11_of_remaining
end Green14MiddleEncoding
