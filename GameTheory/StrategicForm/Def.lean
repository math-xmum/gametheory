import Mathlib

section

variable (Player : Type*) (Outcome : Type*)

structure StrategicGame Player Outcome where
  Strategy : Player → Type u         -- the space of pure strategies for each player
  strategy_nonempty : ∀ i, Nonempty (Strategy i) -- each strategy set is nonempty
  outcome : Player → (Π i, Strategy i) → Outcome
  -- the outcome for a given strategy profile

attribute [instance] StrategicGame.strategy_nonempty

namespace StrategicGame

variable {Player Outcome : Type*} {G : StrategicGame Player Outcome} [DecidableEq Player]


variable {k}  [PartialOrder k] (payoff : Outcome → k)

-- Nash Equilibrium: No single player can unilaterally change their strategy for better payoff
def NashEquilibrium
 (x :  (i : Player) → G.Strategy i) : Prop :=
  ∀ (i : Player) (si' : G.Strategy i),
    let y := Function.update x i si'
    payoff (G.outcome i x) ≥ payoff (G.outcome i y)

def isFintypeStrategy := ∀ i, Fintype (G.Strategy i)

end StrategicGame



end
