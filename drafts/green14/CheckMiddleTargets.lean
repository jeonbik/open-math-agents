import MiddleAdapter
import Mathlib.Order.Interval.Finset.Nat
open Std.Sat Green14MiddleEncoding Green14MiddleTarget
namespace OMA.R_Green14_W_3_13_R1_H1_R1
def H1 : Prop :=
  ∀ L R : Finset ℕ, L ⊆ Finset.Icc 1 79 → R ⊆ Finset.Icc 1 79 → Disjoint L R →
    let red (x : ℕ) := x = 79 ∨ (x < 79 ∧ 79-x ∈ L) ∨ (79 < x ∧ x-79 ∈ R)
    (∀ a d : ℕ, 0 < d → a+2*d ≤ 158 → a+d ≠ 79 →
      red a → red (a+d) → red (a+2*d) → False) →
    ∃ a d : ℕ, 0 < d ∧ a+12*d ≤ 158 ∧ ∀ t : Fin 13, ¬red (a+t.val*d)

/-- On 158 positions the right radius two is absent. -/
def H2 : Prop :=
  ∀ L R : Finset ℕ, L ⊆ Finset.Icc 1 78 → R ⊆ Finset.Icc 1 79 → Disjoint L R → 2 ∉ R →
    let red (x : ℕ) := x = 78 ∨ (x < 78 ∧ 78-x ∈ L) ∨ (78 < x ∧ x-78 ∈ R)
    (∀ a d : ℕ, 0 < d → a+2*d ≤ 157 → a+d ≠ 78 →
      red a → red (a+d) → red (a+2*d) → False) →
    ∃ a d : ℕ, 0 < d ∧ a+12*d ≤ 157 ∧ ∀ t : Fin 13, ¬red (a+t.val*d)


theorem h1_of_unsat (unsat : h11.Unsat) : H1 := by
  intro L R _ _ disjoint red noTriple
  dsimp only [red] at noTriple ⊢
  exact finishH1 unsat L R disjoint noTriple

theorem h2_of_unsat (unsat : h12.Unsat) : H2 := by
  intro L R _ _ disjoint excluded red noTriple
  dsimp only [red] at noTriple ⊢
  exact finishH2 unsat L R disjoint excluded noTriple

end OMA.R_Green14_W_3_13_R1_H1_R1
#print axioms OMA.R_Green14_W_3_13_R1_H1_R1.h1_of_unsat
#print axioms OMA.R_Green14_W_3_13_R1_H1_R1.h2_of_unsat
