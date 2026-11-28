import Std.Sat.CNF.Basic
import Std.Sat.CNF.Dimacs

open Std.Sat

namespace Green14MiddleEncoding

-- The red triples through the fixed red center are represented by binary clauses.
def rows (limit length : Nat) (keep : Nat → Nat → Bool) (sign : Bool) :
    List (CNF.Clause Nat) :=
  (List.range limit).flatMap fun i =>
    ((List.range (limit + 1)).filter fun a =>
      decide (a + (length - 1) * (i+1) ≤ limit) && keep a (i+1)).map fun a =>
      (List.range length).map fun t => (a+t*(i+1), sign)

theorem rows_eval {limit length : Nat} {keep : Nat → Nat → Bool} {sign : Bool}
    (red : Nat → Bool)
    (witness : ∀ a d, 0 < d → a + (length-1)*d ≤ limit → keep a d = true →
      ∃ t < length, red (a+t*d) = sign) :
    ∀ row ∈ rows limit length keep sign, row.eval red = true := by
  intro row hrow
  simp only [rows, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq] at hrow
  obtain ⟨i, _, a, ⟨_, hlimit, hkeep⟩, rfl⟩ := hrow
  obtain ⟨t, ht, hred⟩ := witness a (i+1) (by omega) hlimit hkeep
  simp only [CNF.Clause.eval, List.any_eq_true]
  refine ⟨(a+t*(i+1), sign), List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩, ?_⟩
  simp [hred]

def centeredRows (limit center : Nat) : List (CNF.Clause Nat) :=
  (List.range (min center (limit-center))).map fun i =>
    [(center-(i+1), false), (center+(i+1), false)]

def formula (limit center : Nat) (extra : List (CNF.Clause Nat)) : CNF Nat :=
  ⟨(rows limit 3 (fun a d => decide (a+d ≠ center)) false ++
    rows limit 13 (fun _ _ => true) true ++
    [[(center, true)]] ++ centeredRows limit center ++ extra).toArray⟩

theorem hasBlueProgression {limit center : Nat} {extra : List (CNF.Clause Nat)}
    (unsat : (formula limit center extra).Unsat) (red : Nat → Bool)
    (anchor : red center = true)
    (noMiddle : ∀ d, 0 < d → d ≤ center → center+d ≤ limit →
      red (center-d) = true → red (center+d) = true → False)
    (noTriple : ∀ a d, 0 < d → a+2*d ≤ limit → a+d ≠ center →
      red a = true → red (a+d) = true → red (a+2*d) = true → False)
    (extraValid : ∀ row ∈ extra, row.eval red = true) :
    ∃ a d, 0 < d ∧ a+12*d ≤ limit ∧ ∀ t : Fin 13, red (a+t.val*d) = false := by
  apply Classical.byContradiction
  intro absent
  have reds : ∀ row ∈ rows limit 3 (fun a d => decide (a+d ≠ center)) false,
      row.eval red = true := by
    apply rows_eval
    intro a d hd hlimit hkeep
    have hne : a+d ≠ center := of_decide_eq_true hkeep
    cases ha : red a
    · exact ⟨0, by decide, by simpa using ha⟩
    cases hb : red (a+d)
    · exact ⟨1, by decide, by simpa using hb⟩
    cases hc : red (a+2*d)
    · exact ⟨2, by decide, hc⟩
    exact (noTriple a d hd hlimit hne ha hb hc).elim
  have blues : ∀ row ∈ rows limit 13 (fun _ _ => true) true, row.eval red = true := by
    apply rows_eval
    intro a d hd hlimit _
    apply Classical.byContradiction
    intro noRed
    apply absent
    refine ⟨a, d, hd, hlimit, ?_⟩
    intro t
    cases ht : red (a+t.val*d)
    · rfl
    · exact (noRed ⟨t.val, t.isLt, ht⟩).elim
  have centered : ∀ row ∈ centeredRows limit center, row.eval red = true := by
    intro row hrow
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
    have hi' := List.mem_range.mp hi
    have := Nat.min_le_left center (limit-center)
    have := Nat.min_le_right center (limit-center)
    cases hl : red (center-(i+1)) <;> cases hr : red (center+(i+1)) <;> simp [hl, hr]
    exact (noMiddle (i+1) (by omega) (by omega) (by omega) hl hr).elim
  have sat : (formula limit center extra).eval red = true := by
    simp only [CNF.eval, Array.all_eq_true_iff_forall_mem, formula, List.mem_toArray,
      List.mem_append]
    intro row hrow
    rcases hrow with ((((h | h) | h) | h) | h)
    · exact reds row h
    · exact blues row h
    · have heq := List.mem_singleton.mp h
      subst row
      simp [anchor]
    · exact centered row h
    · exact extraValid row h
  rw [unsat red] at sat
  contradiction

def h11 : CNF Nat := formula 158 79 []
def h12 : CNF Nat := formula 157 78 [[(80, false)]]

#print axioms hasBlueProgression

end Green14MiddleEncoding
