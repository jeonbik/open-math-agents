import TraceObligation
open Green14ReflectedCertificate Std.Tactic.BVDecide
def probe : Std.Sat.CNF Nat := ⟨leftFormula.clauses.push [(79,false)]⟩
set_option maxRecDepth 500000 in
set_option maxHeartbeats 500000 in
theorem probeCheck : LRAT.check #[.addEmpty 7220 #[7138,7219]] probe = true := by decide +kernel
