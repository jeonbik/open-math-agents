import Std
namespace Green14Reflection
def Avoid (r : Nat → Prop) : Prop :=
  ∀ a d, 0 < d → a+2*d ≤ 158 → ¬ (r a ∧ r (a+d) ∧ r (a+2*d))
def Blue (r : Nat → Prop) : Prop :=
  ∃ a d, 0 < d ∧ a+12*d ≤ 158 ∧ ∀ t : Fin 13, ¬r (a+t.val*d)
def rev (r : Nat → Prop) (x : Nat) := r (158-x)
theorem avoid_rev {r} (h : Avoid r) : Avoid (rev r) := by
  intro a d hd hb ⟨ha,hm,he⟩
  apply h (158-(a+2*d)) d hd (by omega)
  unfold rev at *
  exact ⟨he, (show 158-(a+2*d)+d = 158-(a+d) by omega) ▸ hm, (show 158-(a+2*d)+2*d = 158-a by omega) ▸ ha⟩
theorem blue_of_rev {r} (h : Blue (rev r)) : Blue r := by
  obtain ⟨a,d,hd,hb,h⟩ := h
  refine ⟨158-(a+12*d),d,hd,by omega,?_⟩
  intro t
  have ht := h (⟨12-t.val,by omega⟩ : Fin 13)
  unfold rev at ht
  have e : (12-t.val)*d + t.val*d = 12*d := by
    rw [← Nat.add_mul]; congr 1; omega
  simpa only [show 158-(a+(12-t.val)*d) = 158-(a+12*d)+t.val*d by omega] using ht
theorem center_reduction
    (oneSide : ∀ r, Avoid r → r 79 → ¬r 78 → Blue r)
    (r) (h : Avoid r) (hc : r 79) : Blue r := by
  classical
  by_cases hl : r 78
  · apply blue_of_rev (r := r)
    apply oneSide _ (avoid_rev h) hc
    intro hr
    exact h 78 1 (by decide) (by decide) ⟨hl,hc,hr⟩
  · exact oneSide r h hc hl
#print axioms center_reduction
end Green14Reflection
