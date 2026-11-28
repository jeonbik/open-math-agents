import ReflectedCertificate
import Std.Tactic.BVDecide.LRAT.Checker
open Green14ReflectedCertificate Std.Tactic.BVDecide
theorem finishFromTrace (actions : Array LRAT.IntAction)
    (checked : LRAT.check actions leftFormula) : ∀ r, Green14Reflection.Avoid r → r 79 → Green14Reflection.Blue r := afterCertificate (LRAT.check_sound actions leftFormula checked)
#print axioms finishFromTrace
