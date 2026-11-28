import Reflection
import MiddleEncoding
open Std.Sat Green14MiddleEncoding Green14Reflection
namespace Green14ReflectedCertificate
def leftFormula := formula 158 79 [[(78,false)]]
theorem afterCertificate (cert : leftFormula.Unsat)
    (r : Nat → Prop) (h : Avoid r) (hc : r 79) : Blue r := by
  apply center_reduction _ r h hc
  intro s hs hc hl
  classical
  let f := fun x => decide (s x)
  have mid : ∀ d, 0 < d → d ≤ 79 → 79+d ≤ 158 →
      f (79-d) = true → f (79+d) = true → False := by
    intro d hd hb he h1 h2
    apply hs (79-d) d hd (by omega)
    have m : 79-d+d=79 := by omega
    have e : 79-d+2*d=79+d := by omega
    simpa [m,e,f] using And.intro (of_decide_eq_true h1) (And.intro hc (of_decide_eq_true h2))
  obtain ⟨a,d,hd,hb,hh⟩ := hasBlueProgression cert f (by simpa [f] using hc) mid
    (fun a d hd hb _ h1 h2 h3 => hs a d hd hb
      ⟨of_decide_eq_true h1,of_decide_eq_true h2,of_decide_eq_true h3⟩)
    (by intro row hr; simp only [List.mem_singleton] at hr; subst row; simp [f,hl])
  exact ⟨a,d,hd,hb,fun t => of_decide_eq_false (hh t)⟩
#print axioms afterCertificate
end Green14ReflectedCertificate
