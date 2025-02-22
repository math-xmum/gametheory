/-  Prisoner's Dilemma in Lean -/
import Mathlib

/- Define the possible strategies: Cooperate or Defect -/
inductive Strategy where
  | Cooperate
  | Defect

open Strategy

/- Define the payoff function, which returns an integer payoff based on the strategies chosen by two players -/
abbrev Payoff (A B : Strategy) : ℤ :=
  match A, B with
  | Cooperate, Cooperate => 1  -- Both cooperate: minimal reward
  | Cooperate, Defect => 0      -- One cooperates, the other defects: cooperator gets nothing
  | Defect, Cooperate => 3      -- One defects, the other cooperates: defector gets the highest reward
  | Defect, Defect => 2         -- Both defect: both get a moderate reward

/- Theorem: The Nash equilibrium condition states that no player can improve their outcome by unilaterally changing their strategy.
   Here, we prove that defecting will never result in a lower payoff than cooperating when the other player cooperates. -/
theorem Nash : ∀ S : Strategy, Payoff Cooperate Cooperate ≤ Payoff S Cooperate := by
  intro S
  -- Case analysis on strategy S
  cases S with
  | Cooperate => rfl  -- If S = Cooperate, Payoff(1,1) ≤ Payoff(1,1) is trivial
  | Defect => decide  -- If S = Defect, we need to show 1 ≤ 3, which is true by numerical comparison
