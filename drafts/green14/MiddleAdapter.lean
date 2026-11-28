import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Interval
import MiddleEncoding

open Std.Sat Green14MiddleEncoding

namespace Green14MiddleTarget

def Red (L R : Finset Nat) (center x : Nat) : Prop :=
  x = center ∨ (x < center ∧ center-x ∈ L) ∨ (center < x ∧ x-center ∈ R)

def paint (L R : Finset Nat) (center x : Nat) : Bool :=
  decide (x = center ∨ (x < center ∧ center-x ∈ L) ∨ (center < x ∧ x-center ∈ R))

theorem paint_true (L R : Finset Nat) (center x : Nat) :
    paint L R center x = true ↔ Red L R center x :=
  by simp [paint, Red]

theorem no_middle (L R : Finset Nat) {center d : Nat} (disjoint : Disjoint L R)
    (hd : 0 < d) (hc : d ≤ center) (hl : paint L R center (center-d) = true)
    (hr : paint L R center (center+d) = true) : False := by
  have inL := (paint_true L R center (center-d)).mp hl
  have inR := (paint_true L R center (center+d)).mp hr
  have llt : center-d < center := by omega
  have rlt : center < center+d := by omega
  have dl : center-(center-d) = d := by omega
  have dr : center+d-center = d := by omega
  simp [Red, show center-d ≠ center by omega, llt, show ¬ center < center-d by omega, dl] at inL
  simp [Red, show d ≠ 0 by omega, show ¬ center+d < center by omega, rlt, dr] at inR
  exact Finset.disjoint_left.mp disjoint inL inR

theorem fromUnsat {limit center : Nat} {extra : List (CNF.Clause Nat)}
    (unsat : (formula limit center extra).Unsat)
    (L R : Finset Nat) (disjoint : Disjoint L R)
    (noTriple : ∀ a d, 0 < d → a+2*d ≤ limit → a+d ≠ center →
      Red L R center a → Red L R center (a+d) → Red L R center (a+2*d) → False)
    (extraValid : ∀ row ∈ extra, row.eval (paint L R center) = true) :
    ∃ a d, 0 < d ∧ a+12*d ≤ limit ∧ ∀ t : Fin 13, ¬ Red L R center (a+t.val*d) := by
  have anchor : paint L R center center = true :=
    (paint_true _ _ _ _).mpr (Or.inl rfl)
  obtain ⟨a, d, hd, hlim, hb⟩ := hasBlueProgression unsat (paint L R center) anchor
    (fun d hd hc _ hl hr => no_middle L R disjoint hd hc hl hr)
    (fun a d hd hb hn h1 h2 h3 => noTriple a d hd hb hn
      ((paint_true _ _ _ _).mp h1) ((paint_true _ _ _ _).mp h2) ((paint_true _ _ _ _).mp h3))
    extraValid
  refine ⟨a,d,hd,hlim, ?_⟩
  intro t hr
  have ht := (paint_true L R center _).mpr hr
  rw [hb t] at ht
  contradiction

theorem finishH1 (unsat : h11.Unsat) (L R : Finset Nat)
    (disjoint : Disjoint L R)
    (noTriple : ∀ a d, 0 < d → a+2*d ≤ 158 → a+d ≠ 79 →
      Red L R 79 a → Red L R 79 (a+d) → Red L R 79 (a+2*d) → False) :
    ∃ a d, 0 < d ∧ a+12*d ≤ 158 ∧ ∀ t : Fin 13, ¬ Red L R 79 (a+t.val*d) :=
  fromUnsat unsat L R disjoint noTriple (by simp)

theorem finishH2 (unsat : h12.Unsat) (L R : Finset Nat)
    (disjoint : Disjoint L R) (excluded : 2 ∉ R)
    (noTriple : ∀ a d, 0 < d → a+2*d ≤ 157 → a+d ≠ 78 →
      Red L R 78 a → Red L R 78 (a+d) → Red L R 78 (a+2*d) → False) :
    ∃ a d, 0 < d ∧ a+12*d ≤ 157 ∧ ∀ t : Fin 13, ¬ Red L R 78 (a+t.val*d) := by
  apply fromUnsat unsat L R disjoint noTriple
  intro row hrow
  change row ∈ ([[(80, false)]] : List (CNF.Clause Nat)) at hrow
  obtain rfl := List.mem_singleton.mp hrow
  have hblue : paint L R 78 80 = false := by
    simp [paint, show ¬ (80 : Nat) < 78 by decide, show (80 : Nat) - 78 = 2 by decide,
      excluded]
  simp [hblue]
end Green14MiddleTarget

#print axioms Green14MiddleTarget.finishH1
#print axioms Green14MiddleTarget.finishH2
