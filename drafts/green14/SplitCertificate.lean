import Std.Sat.CNF.Basic

open Std.Sat

namespace Green14MiddleEncoding

def withLiteral (f : CNF Nat) (v : Nat) (b : Bool) : CNF Nat :=
  ⟨f.clauses.push [(v, b)]⟩

theorem split_unsat (f : CNF Nat) (v : Nat)
    (negative : (withLiteral f v false).Unsat)
    (positive : (withLiteral f v true).Unsat) : f.Unsat := by
  intro assignment
  cases h : assignment v <;>
    first | simpa [withLiteral, CNF.eval, CNF.Clause.eval, h] using negative assignment
          | simpa [withLiteral, CNF.eval, CNF.Clause.eval, h] using positive assignment

#print axioms split_unsat
end Green14MiddleEncoding
