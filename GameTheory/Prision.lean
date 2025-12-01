/- Prisoner's dilemma -/
import Mathlib
inductive Strategy where
  | Cooperate
  | Defect
open Strategy
abbrev Payoff (A B : Strategy) : ℤ :=
  match A,B with
  | Cooperate, Cooperate => 1
  | Cooperate, Defect => 0
  | Defect, Cooperate => 3
  | Defect, Defect => 2

/-- The Nash equilibrium is both sides Cooperate--/
theorem Nash : ∀ S : Strategy , 
  Payoff Cooperate Cooperate ≤  Payoff S Cooperate := by
  sorry 


