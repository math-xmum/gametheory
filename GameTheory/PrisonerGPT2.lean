import Mathlib.Data.Finset.Basic

-- Define the actions
inductive Action
| C  -- Cooperate
| D  -- Defect

deriving DecidableEq

-- Define a type for players
inductive Player
| P1
| P2

deriving DecidableEq

-- Define the payoff function
-- This is the standard Prisoner's Dilemma matrix
-- Returns a tuple (payoff for P1, payoff for P2)
def payoff (a1 a2 : Action) : ℤ × ℤ :=
  match a1, a2 with
  | Action.C, Action.C => (-1, -1)
  | Action.C, Action.D => (-3, 0)
  | Action.D, Action.C => (0, -3)
  | Action.D, Action.D => (-2, -2)

-- Define a strategy as a function from opponent's action to own action
def best_response (p : Player) (opp_action : Action) : Action :=
  match p, opp_action with
  | Player.P1, Action.C => Action.D
  | Player.P1, Action.D => Action.D
  | Player.P2, Action.C => Action.D
  | Player.P2, Action.D => Action.D

-- A strategy profile is a Nash equilibrium if no player benefits from deviating
def is_nash_equilibrium (s1 s2 : Action) : Prop :=
  let (u1, u2) := payoff s1 s2
  let (u1', _) := payoff (best_response Player.P1 s2) s2
  let (_, u2') := payoff s1 (best_response Player.P2 s1)
  u1 ≥ u1' ∧ u2 ≥ u2'

-- Prove that (D, D) is a Nash equilibrium
theorem prisoners_dilemma_nash : is_nash_equilibrium Action.D Action.D :=
by
  simp [is_nash_equilibrium, best_response, payoff]
